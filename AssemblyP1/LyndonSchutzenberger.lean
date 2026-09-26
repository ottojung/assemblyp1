import AssemblyP1.AmpBmpPrimitivity

/-!
# The Lyndon–Schützenberger theorem (self-contained)

This module closes the residual word-combinatorics step of issue #92.

`AssemblyP1.AmpBmpPrimitivity` proves the *conditional* statement that a witness
`A^m ++ B^m = U^k` (with `m, k >= 2`) forces `A`, `B`, `U` to be powers of one
common word, but only under the extra length hypothesis
`(m-1)*|A| >= |U|`.  That hypothesis is genuinely not available for the
branching construction of `docs/scalar-primitive-spellings-83.md`: it fails for
every *square* witness `k = 2` with `|A| = |B|`, and more generally whenever the
two excursions have nearly equal length.

The missing input is the classical theorem of Lyndon and Schützenberger (1965):
if `x^a ++ y^b = z^c` with `a, b, c >= 2`, then `x`, `y` and `z` are powers of
one common word.  It is proved here from scratch, on top of the Fine–Wilf
theorem of `AssemblyP1.WordPeriodicity` only.  No Lyndon–Schützenberger-type
statement is ever assumed; the only external input is the kernel-checked
Fine–Wilf gcd-period theorem.

## Structure of the proof (following Lyndon–Schützenberger 1965 / Lothaire 1.3.2)

Let `x^a ++ y^b = z^c` with `a, b, c >= 2` and `x, y` nonempty.  Put
`d = |x|`, `e = |y|`, `f = |z|`, so `a*d + b*e = c*f`.

* **Symmetry.** By reversing the word, the equation becomes
  `(rev y)^b ++ (rev x)^a = (rev z)^c`, and `rev p ++ rev q = rev q ++ rev p`
  is equivalent to `p ++ q = q ++ p`.  Hence we may assume `b*e <= a*d`, and the
  induction measure `f + b*e` strictly decreases when we pass to the reversed
  instance.

* **Case 1 (the periodicity lemma).** If `a*d >= f + d`, i.e.
  `(a-1)*d >= f`, then `ampbmp_commonRoot` applies directly.  Symmetrically, if
  `b*e >= f + e` the reversed equation is handled by the same lemma.

* **Case 2 (`c = 3`, the core case; proved as `LS_core_c3`).** If `a*d < f + d` and `b*e < f + e` then
  `c < 4`.  For `c = 3` one first derives `a = 2` and `d < f < 2*d`, and then
  the *critical decomposition* of the word: with `u` a border of `x` and `w` the
  remaining factor, `x = u ++ w = w ++ v`, `z = w ++ v ++ u` and
  `y^b = v ++ u ++ w ++ v ++ u`.  The word `s = u ++ w ++ v` is then simultaneously
  `|u|`-periodic (it is `u ++ u ++ w`) and `|y|``-periodic (it is a factor of
  `y^b`), and `|u| + e <= f`; Fine–Wilf gives the period
  `g = gcd |u| e`, and `g` divides `|x|`, `|z|`, `|u|`, `|v|`, `|w|`, so
  `x`, `y^b` and `z` are all powers of the length-`g` prefix of `s`.  Hence
  `x` and `y` are powers of a common word.

* **Case 3 (`c = 2`).** Write `z = x^(a-1) ++ u` and `z = w ++ y^b` (both
  splits exist, and are proper/nonempty in the relevant directions).  Cancellations
  give `x = u ++ w`, whence `w^2 ++ y^b = (w ++ u)^a` is *another* solution of the
  same equation, with right-hand base `w ++ u` of length `|x| < |z|`; the
  induction hypothesis applies and yields `w ++ y = y ++ w`, from which
  `x ++ y = y ++ x` follows.

## Main results

* `LS_core_c3` — the `c = 3` core case above.
* `lyndonSchutzenberger` — for `a, b, c >= 2`,
  `x^a ++ y^b = z^c` implies `x ++ y = y ++ x`.
* `ampbmp_commonRoot_uncond` — **the theorem needed by issue #92**: for nonempty
  `A, B` and `m >= 2`, if `A^m ++ B^m` is a proper power `U^k` (`k >= 2`) then
  `A`, `B` and `U` are powers of one common nonempty word.
* `ampbmp_head_eq_of_pow_uncond`, `ampbmp_primitive_of_head_ne_uncond` — the
  separator theorems: two excursions whose first letters differ produce
  `A^m ++ B^m` primitive for every `m >= 2`.

## Status

* **Done, machine-checked:** all the auxiliary word lemmas and `LS_core_c3`, the
  `c = 3` core case (including the Fine–Wilf step and the extraction of the
  common root).
* **Not yet present:** `lyndonSchutzenberger` and the four `_uncond` corollaries
  above.  What remains is the induction over the cases listed in
  `## Structure of the proof`: the reverse-symmetry reduction, Case 1 (which
  invokes the existing `ampbmp_commonRoot`), and Case 3 (the `c = 2` descent).
  Until those are added, `LS_core_c3` is the only theorem in this file, and
  `AssemblyP1.AmpBmpPrimitivity` still carries its extra length hypothesis.

No `sorry`, no `admit`, no new axioms.
-/

namespace AssemblyP1

open List

variable {α : Type _}

/-! ## Reversal: the symmetry `x^a y^b = z^c` <-> `(rev y)^b (rev x)^a = (rev z)^c` -/

/-- A power of a word can be extended on either side. -/
@[simp] theorem nCopies_one (l : List α) : nCopies l 1 = l := by
  rw [nCopies_succ, nCopies_zero, List.append_nil]

theorem nCopies_add_right (l : List α) (k : ℕ) : l ++ nCopies l k = nCopies l k ++ l := by
  have h1 : l ++ nCopies l k = nCopies l (1 + k) := calc
    l ++ nCopies l k = nCopies l 1 ++ nCopies l k := by rw [nCopies_one]
    _ = nCopies l (1 + k) := (nCopies_add l 1 k).symm
  have h2 : nCopies l k ++ l = nCopies l (k + 1) := calc
    nCopies l k ++ l = nCopies l k ++ nCopies l 1 := by rw [nCopies_one]
    _ = nCopies l (k + 1) := (nCopies_add l k 1).symm
  rw [h1, h2, show 1 + k = k + 1 from by omega]

theorem rev_nCopies (l : List α) : ∀ k : ℕ, (nCopies l k).reverse = nCopies l.reverse k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [nCopies_succ, List.reverse_append, ih, nCopies_succ, nCopies_add_right l.reverse k]

/-- `rev p ++ rev q = rev q ++ rev p` is exactly `p ++ q = q ++ p`. -/
theorem comm_of_rev_comm {p q : List α} (h : p.reverse ++ q.reverse = q.reverse ++ p.reverse) :
    p ++ q = q ++ p := by
  have h1 : (p ++ q).reverse = (q ++ p).reverse := calc
    (p ++ q).reverse = q.reverse ++ p.reverse := List.reverse_append ..
    _ = p.reverse ++ q.reverse := h.symm
    _ = (q ++ p).reverse := (List.reverse_append).symm
  exact List.reverse_inj.mp h1

theorem rev_comm_of_comm {p q : List α} (h : p ++ q = q ++ p) :
    p.reverse ++ q.reverse = q.reverse ++ p.reverse := by
  calc p.reverse ++ q.reverse = (q ++ p).reverse := (List.reverse_append).symm
    _ = (p ++ q).reverse := by rw [h]
    _ = q.reverse ++ p.reverse := List.reverse_append ..

/-! ## Small arithmetic helpers -/

theorem add_two_mul (a b : ℕ) : a * b + a * b = a * b * 2 := by
  calc a * b + a * b = (a + a) * b := (Nat.add_mul a a b).symm
    _ = (2 * a) * b := by rw [Nat.two_mul a]
    _ = 2 * (a * b) := Nat.mul_assoc 2 a b
    _ = a * b * 2 := Nat.mul_comm 2 (a * b)

theorem le_mul_add' {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) : b + a ≤ a * b := by
  have h1 : a = (a - 1).succ := by omega
  have h2 : (a - 1) * 2 ≤ (a - 1) * b := Nat.mul_le_mul_left (a - 1) hb
  have h3 : a ≤ (a - 1) * 2 := by omega
  have h4 : a ≤ (a - 1) * b := Nat.le_trans h3 h2
  have h5 : a * b = (a - 1) * b + b := by
    have h6 := congrArg (fun t : ℕ => t * b) h1
    rwa [Nat.succ_mul] at h6
  calc b + a ≤ b + (a - 1) * b := Nat.add_le_add_left h4 b
    _ = a * b := by
      calc b + (a - 1) * b = (a - 1) * b + b := Nat.add_comm ..
        _ = a * b := h5.symm

theorem mul_le_mul_fst {a n m : ℕ} (h : n * a ≤ m * a) : a * n ≤ a * m := by
  rw [Nat.mul_comm a n, Nat.mul_comm a m] at ⊢
  exact h

/-! ## Equal powers have a common root

The workhorse: two powers of a common word (`x^m = w^p`, `m, p >= 1`) are powers
of one common word.  This is the standard "equality of two powers" lemma; it is
proved here from Fine–Wilf (case `p >= 2`) and by inspection (cases `m = 1`,
`p = 1`). -/

/-- Congruence for append: the hypotheses are used only on the outer occurrences. -/
theorem append_congr {l₁ l₂ m₁ m₂ : List α} (h1 : l₁ = m₁) (h2 : l₂ = m₂) :
    l₁ ++ l₂ = m₁ ++ m₂ := by rw [h1, h2]

/-- If `g` divides both `a` and `b`, then `(a + b) / g = a / g + b / g`. -/
theorem dvd_add_div {g a b : ℕ} (hg : 0 < g) (h1 : g ∣ a) (h2 : g ∣ b) :
    (a + b) / g = a / g + b / g := by
  have h3 : a = g * (a / g) := (Nat.mul_div_cancel' h1).symm
  have h4 : b = g * (b / g) := (Nat.mul_div_cancel' h2).symm
  have h5 : a + b = g * (a / g + b / g) := by
    calc a + b = g * (a / g) + g * (b / g) := congrArg₂ (· + ·) h3 h4
      _ = g * (a / g + b / g) := (Nat.mul_add ..).symm
  have h6 : a + b = g * ((a + b) / g) := (Nat.mul_div_cancel' (Nat.dvd_add h1 h2)).symm
  exact Nat.mul_left_cancel hg (h6.symm.trans h5)

theorem eqPow_commonRoot {x w : List α} {m p : ℕ} (hx : x ≠ []) (hw : w ≠ [])
    (hm : 1 ≤ m) (hp : 1 ≤ p) (h : nCopies x m = nCopies w p) :
    ∃ r : List α, r ≠ [] ∧ ∃ i j : ℕ, 1 ≤ i ∧ 1 ≤ j ∧ x = nCopies r i ∧ w = nCopies r j := by
  have hxw : x.length ≤ (nCopies w p).length := by
    rw [← h]; exact length_le_nCopies_length hm
  by_cases hpm : p = 1
  · refine ⟨x, hx, 1, m, by omega, hm, (nCopies_one x).symm, ?_⟩
    calc w = nCopies w 1 := (nCopies_one w).symm
      _ = nCopies w p := by rw [hpm]
      _ = nCopies x m := h.symm
  by_cases hmi : m = 1
  · refine ⟨w, hw, p, 1, hp, by omega, ?_, (nCopies_one w).symm⟩
    have h1 := h
    rw [hmi] at h1
    calc x = nCopies x 1 := (nCopies_one x).symm
      _ = nCopies w p := h1
  have hm2 : 2 ≤ m := by omega
  have hp2 : 2 ≤ p := by omega
  have hprod : m * x.length = p * w.length := by
    have h2 := congrArg List.length h
    rwa [nCopies_length, nCopies_length] at h2
  have hprod' : x.length * m = p * w.length := by
    rw [← Nat.mul_comm m x.length]; exact hprod
  -- the word `w^p` has period `g = gcd |x| |w|`
  have hsum : x.length + w.length ≤ (nCopies w p).length := by
    have h3 : m * (x.length + w.length) = p * w.length + m * w.length := by
      rw [Nat.mul_add, hprod]
    have hpm : p + m ≤ m * p := le_mul_add' hm2 hp2
    have h4 : p * w.length + m * w.length ≤ m * (p * w.length) := by
      have h5 : p * w.length + m * w.length = (p + m) * w.length := (Nat.add_mul p m w.length).symm
      have h6 : (p + m) * w.length ≤ w.length * (m * p) := by
        calc (p + m) * w.length = w.length * (p + m) := Nat.mul_comm _ _
          _ ≤ w.length * (m * p) := Nat.mul_le_mul_left w.length hpm
      have h7 : w.length * (m * p) = m * (p * w.length) := by
        have h7' : w.length * (m * p) = (w.length * m) * p := (Nat.mul_assoc w.length m p).symm
        have h7'' : (w.length * m) * p = m * (w.length * p) := by
          have h7b : w.length * (m * p) = m * (w.length * p) := Nat.mul_left_comm w.length m p
          rw [h7'] at h7b; exact h7b
        have h7''' : m * (w.length * p) = m * (p * w.length) := by
          congr 1; exact Nat.mul_comm w.length p
        rw [h7', h7'', h7''']
      calc p * w.length + m * w.length = (p + m) * w.length := h5
        _ ≤ w.length * (m * p) := h6
        _ = m * (p * w.length) := h7
    have h8 : m * (x.length + w.length) ≤ m * (p * w.length) := by rw [h3]; exact h4
    have h9 : x.length + w.length ≤ p * w.length := Nat.le_of_mul_le_mul_left h8 (by omega)
    have h9' : x.length + w.length ≤ (nCopies w p).length := by
      rw [nCopies_length]; exact h9
    exact h9'
  have hlen : w.length + x.length - Nat.gcd w.length x.length ≤ (nCopies w p).length := by
    have h1 : w.length + x.length - Nat.gcd w.length x.length ≤ w.length + x.length := by omega
    have h2 : w.length + x.length ≤ (nCopies w p).length := by
      rw [Nat.add_comm]; exact hsum
    exact h1.trans h2
  have hper : Period (nCopies w p) (Nat.gcd w.length x.length) := by
    have hperx : Period (nCopies w p) x.length := by
      have h2 : Period (nCopies x m) x.length := nCopies_period x m hx hm
      rw [← h]; exact h2
    exact (nCopies_period w p hw hp).fineWilf hperx hlen
  set g := Nat.gcd w.length x.length with hg
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) (length_pos_of_ne_nil hw)
  have hgdivw : g ∣ w.length := by simpa [hg] using (Nat.gcd_dvd_left w.length x.length)
  have hgdivx : g ∣ x.length := by simpa [hg] using (Nat.gcd_dvd_right w.length x.length)
  have hgdlew : g ≤ w.length := dvd_le_of_pos (length_pos_of_ne_nil hw) hgdivw
  have hgplex : g ≤ x.length := dvd_le_of_pos (length_pos_of_ne_nil hx) hgdivx
  have hperw : Period w g := by
    have h1 := hper.prefix (T := w.length) (length_le_nCopies_length hp)
    rwa [take_nCopies w p hp] at h1
  have hperx : Period x g := by
    have h1 := hper.prefix (T := x.length) hxw
    have h1' : (nCopies w p).take x.length = x := by
      have h2 : (nCopies w p).take x.length = (nCopies x m).take x.length := by rw [h]
      rw [h2, take_nCopies x m hm]
    rwa [h1'] at h1
  have hpoww : w = nCopies (w.take g) (w.length / g) :=
    eq_nCopies_of_period_div hgpos hperw hgdivw hw
  have hpowx : x = nCopies (x.take g) (x.length / g) :=
    eq_nCopies_of_period_div hgpos hperx hgdivx hx
  have htake : x.take g = w.take g := by
    have hxw' : x = (nCopies w p).take x.length := by rw [← h]; exact (take_nCopies x m hm).symm
    have h1 : x.take g = (nCopies w p).take g := by
      nth_rewrite 1 [hxw']
      exact take_take' hgplex
    have h2 : w.take g = (nCopies w p).take g := by
      nth_rewrite 1 [(take_nCopies w p hp).symm]
      exact take_take' hgdlew
    rw [h1, h2]
  refine ⟨w.take g, ne_nil_of_length_pos (by rw [List.length_take, Nat.min_eq_left hgdlew]; exact hgpos),
    x.length / g, w.length / g, ?_, ?_, ?_, ?_⟩
  · exact Nat.succ_le_of_lt (Nat.div_pos hgplex hgpos)
  · exact Nat.succ_le_of_lt (Nat.div_pos hgdlew hgpos)
  · rw [← htake]; exact hpowx
  · exact hpoww

/-- The `x^a y^b = y^b x^a` case of commutation. -/
theorem comm_of_powComm {x y : List α} {a b : ℕ} (hx : x ≠ []) (hy : y ≠ [])
    (ha : 1 ≤ a) (hb : 1 ≤ b) (h : nCopies x a ++ nCopies y b = nCopies y b ++ nCopies x a) :
    x ++ y = y ++ x := by
  have hne : nCopies x a ≠ [] := ne_nil_nCopies hx ha
  have hne' : nCopies y b ≠ [] := ne_nil_nCopies hy hb
  obtain ⟨c, hc, r, s, hr, hs, hxr, hys⟩ :=
    commuting_commonRoot (x := nCopies x a) (y := nCopies y b) hne hne' h
  obtain ⟨α, hα, i, j, hi, hj, hxα, hcα⟩ := eqPow_commonRoot hx hc ha hr hxr
  obtain ⟨β, hβ, i', j', hi', hj', hyβ, hcβ⟩ := eqPow_commonRoot hy hc hb hs hys
  have hcc : nCopies α j = nCopies β j' := by rw [← hcα, ← hcβ]
  obtain ⟨γ, hγ, p, q, hp, hq, hαγ, hβγ⟩ :=
    eqPow_commonRoot hα hβ hj hj' hcc
  have hxg : x = nCopies γ (p * i) := by
    rw [hxα, hαγ, nCopies_compose]
  have hyg : y = nCopies γ (q * i') := by
    rw [hyβ, hβγ, nCopies_compose]
  rw [hxg, hyg, ← nCopies_add, ← nCopies_add, Nat.add_comm]

/-! ## More list-level helpers used in the core case -/

/-- `take` of a concatenation that reaches into the second block. -/
theorem take_append_of_le' {l₁ l₂ : List α} {n : ℕ} (h : l₁.length ≤ n) :
    (l₁ ++ l₂).take n = l₁ ++ l₂.take (n - l₁.length) := by
  rw [List.take_append, List.take_of_length_le h]

/-- `drop` of a concatenation that stays inside the first block. -/
theorem drop_append_of_le' {l₁ l₂ : List α} {n : ℕ} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).drop n = l₁.drop n ++ l₂ := by
  calc (l₁ ++ l₂).drop n = l₁.drop n ++ l₂.drop (n - l₁.length) := List.drop_append ..
    _ = l₁.drop n ++ l₂ := by rw [Nat.sub_eq_zero_of_le (by omega), List.drop_zero]

/-- A prefix window of a concatenation, phrased as an equation for `W`. -/
theorem window_take (W A B : List α) (n : ℕ) (h : W = A ++ B) :
    W.take n = A.take n ++ B.take (n - A.length) := by rw [h, List.take_append]

/-- A suffix window of a concatenation, phrased as an equation for `W`. -/
theorem window_drop (W A B : List α) (n : ℕ) (h : W = A ++ B) :
    W.drop n = A.drop n ++ B.drop (n - A.length) := by rw [h, List.drop_append]

/-- If a word is `u ++ x`, where `x = u ++ w` and the first `|w|` letters of `x`
form `w` again, then the word is `|u|`-periodic.  This is the step that makes
the critical word of the `c = 3` core case `|u|`-periodic. -/
theorem Period.of_two_blocks {s x u w : List α} (hs : s = u ++ x) (hx : x = u ++ w)
    (hwtake : x.take w.length = w) : Period s u.length := by
  intro i hi
  rw [hs] at hi ⊢
  have hlen : (u ++ x).length = u.length + x.length := List.length_append
  have hi1 : i + u.length < u.length + x.length := by rwa [hlen] at hi
  have hxlen : x.length = u.length + w.length := by rw [hx]; exact List.length_append
  have hix : i < x.length := by omega
  by_cases h1 : i < u.length
  · rw [List.getElem?_append, ite_eq_left h1, List.getElem?_append,
      ite_eq_right (by omega : ¬ i + u.length < u.length)]
    have h3 : i + u.length - u.length = i := by omega
    rw [h3, hx, List.getElem?_append, ite_eq_left h1]
  · rw [List.getElem?_append, ite_eq_right h1, List.getElem?_append,
      ite_eq_right (by omega : ¬ i + u.length < u.length)]
    have h2 : i - u.length < w.length := by omega
    have h3 : i + u.length - u.length = i := by omega
    rw [h3]
    have h6 : x[i]? = w[i - u.length]? := by
      rw [hx, List.getElem?_append, ite_eq_right (by omega : ¬ i < u.length)]
    have h5 : x[i - u.length]? = w[i - u.length]? := by
      rw [← hwtake, List.getElem?_take, ite_eq_left h2]
    rw [h5, h6]

/-- Two `d`-periodic words that are aligned modulo `d` share their first `d`
letters. -/
theorem take_eq_of_mod_period {w : List α} {g s : ℕ} (hg : 0 < g) (per : Period w g)
    (hs : g ∣ s) (hle : s + g ≤ w.length) : (w.drop s).take g = w.take g := by
  have hmod : ∀ j : ℕ, (s + j) % g = j % g := by
    intro j
    obtain ⟨k, hk⟩ := hs
    rw [← Nat.add_comm, hk, Nat.add_mul_mod_self_left]
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_drop, List.getElem?_take]
  by_cases h1 : i < g
  · rw [ite_eq_left h1, ite_eq_left h1]
    have h2 : s + i < w.length := by omega
    have h3 := per.of_mod hg (s + i) h2
    rw [h3, hmod i, Nat.mod_eq_of_lt h1]
  · rw [ite_eq_right h1, ite_eq_right h1]


/-! ## The `c = 3` core case of Lyndon–Schützenberger

The critical configuration.  Assume `x^2 ++ y^b = z^3` with `b >= 2`,
`b*|y| <= 2|x|`, `|x| < |z|`, and put `d = |x|`, `e = |y|`, `f = |z|`.  The
periodicity lemma forces `f < 2*d`, and then the two descriptions of the word
(the `x^2 ++ y^b` one and the `z^3` one) force the *critical decomposition*

* `z = x ++ u` where `u` is a border of `x`,
* `x = u ++ w = w ++ p`,
* `y^b = p ++ u ++ z`.

The word `s = u ++ w ++ p` is then simultaneously `|u|`-periodic and `|y|`-
periodic, and `|u| + |y| <= |s|`, so Fine--Wilf applies. -/

theorem LS_core_c3 {x y z : List α} {b : ℕ}
    (hx : x ≠ []) (hy : y ≠ []) (hb : 2 ≤ b)
    (hbe : b * y.length ≤ 2 * x.length)
    (hdx : 2 * x.length < z.length + x.length)
    (h : nCopies x 2 ++ nCopies y b = nCopies z 3) :
    x ++ y = y ++ x := by
  have hxpos : 0 < x.length := length_pos_of_ne_nil hx
  have hypos : 0 < y.length := length_pos_of_ne_nil hy
  have hlen : 2 * x.length + b * y.length = 3 * z.length := by
    have h2 := congrArg List.length h
    rwa [List.length_append, nCopies_length, nCopies_length, nCopies_length] at h2
  have hzpos : 0 < z.length := by
    by_contra hcon
    have hcon' : z.length = 0 := by omega
    rw [hcon'] at hlen
    omega
  have hz : z ≠ [] := ne_nil_of_length_pos hzpos
  have hdf : x.length < z.length := by omega
  have hed : y.length ≤ x.length := by
    have h1 : y.length * 2 ≤ y.length * b := Nat.mul_le_mul_left y.length hb
    have hbe2 : y.length * b ≤ x.length * 2 := by
      have h5 := hbe
      rwa [Nat.mul_comm b y.length, Nat.mul_comm 2 x.length] at h5
    have h2 : y.length * 2 ≤ x.length * 2 := h1.trans hbe2
    rcases Nat.eq_zero_or_pos y.length with hzero | hy2
    · rw [hzero] at h2; omega
    · exact Nat.le_of_mul_le_mul_right h2 (by omega)
  have hf2d : z.length < 2 * x.length := by
    have h1 : 3 * z.length ≤ 4 * x.length := by rw [← hlen]; omega
    omega
  -- the three critical blocks
  set u := x.take (z.length - x.length) with hu
  set w := x.drop (z.length - x.length) with hw
  set p := x.drop (2 * x.length - z.length) with hp
  have hfu : 0 < z.length - x.length := by omega
  have hfu_le : z.length - x.length ≤ x.length := by omega
  have hfw : 0 < 2 * x.length - z.length := by omega
  have hfw_le : 2 * x.length - z.length ≤ x.length := by omega
  have hful : u.length = z.length - x.length := by
    have h1 := hu
    rw [h1, List.length_take, Nat.min_eq_left hfu_le]
  have hwl : w.length = 2 * x.length - z.length := by
    have h1 := hw
    rw [h1, List.length_drop]; omega
  have hpl : p.length = z.length - x.length := by
    have h1 := hp
    rw [h1, List.length_drop]; omega
  have hsplit : u ++ w = x := by rw [hu, hw]; exact List.take_append_drop _ _
  have hx2 : nCopies x 2 = x ++ x := by
    rw [nCopies_succ, nCopies_succ]; simp
  have hx2len : (nCopies x 2).length = 2 * x.length := nCopies_length _ _
  have hz3 : nCopies z 3 = (z ++ z) ++ z := by
    rw [nCopies_succ, nCopies_succ, List.append_assoc]; simp
  -- (1) `z = x ++ u`
  have hzA : z = x ++ u := by
    have h1 : z = (nCopies z 3).take z.length := (take_nCopies z 3 (by omega)).symm
    have h2 : z.length - 2 * x.length = 0 := by omega
    have h3 : (nCopies y b).take 0 = [] := by rw [List.take_zero]
    have h4 := hu
    refine (h1.trans ?_)
    rw [← h]
    rw [List.take_append, hx2len, h2, h3, List.append_nil]
    rw [hx2, List.take_append, List.take_of_length_le (by omega)]
  -- (2) `y^b = p ++ u ++ z`
  have hzd : z.drop (2 * x.length - z.length) = p ++ u := by
    calc z.drop (2 * x.length - z.length) = (x ++ u).drop (2 * x.length - z.length) := by
          rw [hzA]
      _ = p ++ u := by rw [drop_append_of_le' (show 2 * x.length - z.length ≤ x.length from hfw_le)]
  have hybB : nCopies y b = p ++ u ++ z := by
    have h1 : nCopies y b = (nCopies z 3).drop (2 * x.length) := by
      have h2 := hx2len
      rw [← h, ← h2, drop_append_length]
    have h2 : (nCopies z 3).drop (2 * x.length) = (p ++ u) ++ z := by
      calc (nCopies z 3).drop (2 * x.length) = ((z ++ z) ++ z).drop (2 * x.length) := by rw [hz3]
        _ = (z ++ z).drop (2 * x.length) ++ z.drop (2 * x.length - (z ++ z).length) :=
          List.drop_append ..
        _ = (z ++ z).drop (2 * x.length) ++ z := by
          rw [show 2 * x.length - (z ++ z).length = 0 by rw [List.length_append]; omega,
            List.drop_zero]
        _ = z.drop (2 * x.length) ++ z.drop (2 * x.length - z.length) ++ z := by
          rw [List.drop_append]
        _ = z.drop (2 * x.length - z.length) ++ z := by
          rw [List.drop_of_length_le (by omega), List.nil_append]
        _ = (p ++ u) ++ z := by rw [hzd]
    exact h1.trans h2
  -- (3) `w ++ y^b = z ++ z`
  have hwyC : w ++ nCopies y b = z ++ z := by
    have hw' := hw
    have h1 : (nCopies z 3).drop z.length = w ++ nCopies y b := by
      have h4 : z.length - 2 * x.length = 0 := by omega
      calc (nCopies z 3).drop z.length = (nCopies x 2 ++ nCopies y b).drop z.length := by rw [← h]
        _ = (nCopies x 2).drop z.length ++ (nCopies y b).drop (z.length - 2 * x.length) := by
          rw [List.drop_append, hx2len]
        _ = (nCopies x 2).drop z.length ++ nCopies y b := by rw [h4, List.drop_zero]
        _ = (x ++ x).drop z.length ++ nCopies y b := by rw [hx2]
        _ = x.drop z.length ++ x.drop (z.length - x.length) ++ nCopies y b := by
          rw [List.drop_append]
        _ = w ++ nCopies y b := by
          rw [List.drop_of_length_le (by omega), List.nil_append]
    have h2 : ((z ++ z) ++ z).drop z.length = z ++ z := by
      calc ((z ++ z) ++ z).drop z.length
          = (z ++ z).drop z.length ++ z.drop (z.length - (z ++ z).length) := List.drop_append ..
        _ = (z ++ z).drop z.length ++ z := by
          rw [show z.length - (z ++ z).length = 0 by rw [List.length_append]; omega, List.drop_zero]
        _ = z.drop z.length ++ z.drop (z.length - z.length) ++ z := by rw [List.drop_append]
        _ = z ++ z := by simp
    calc w ++ nCopies y b = (nCopies z 3).drop z.length := h1.symm
      _ = ((z ++ z) ++ z).drop z.length := by rw [hz3]
      _ = z ++ z := h2
  -- (4) `x = w ++ p`
  have hx_wp : x = w ++ p := by
    have h1' : w ++ ((p ++ u) ++ z) = z ++ z := by rw [← hybB, hwyC]
    have h2 : w ++ (p ++ u) = z := by
      have hB : (w ++ (p ++ u)) ++ z = z ++ z := by rw [List.append_assoc]; exact h1'
      exact List.append_cancel_right hB
    have h3 : (w ++ p) ++ u = x ++ u := by
      rw [← List.append_assoc] at h2
      rw [hzA] at h2
      exact h2
    exact (List.append_cancel_right h3).symm
  -- (5) the first `|w|` letters of `x` are `w`
  have hwtake : x.take w.length = w := by
    have h1 : (w ++ p).take w.length = w := calc
      (w ++ p).take w.length = w.take w.length ++ p.take (w.length - w.length) := by
        rw [List.take_append]
      _ = w ++ [] := by
        rw [List.take_of_length_le (by omega), show w.length - w.length = 0 by omega,
          List.take_zero]
      _ = w := by rw [List.append_nil]
    rw [← hx_wp] at h1
    exact h1
  -- (6) the critical word `s = u ++ w ++ p` and its two periods
  set s := u ++ w ++ p with hs
  have hslen : s.length = z.length := by
    have h1 := hs
    rw [h1, List.length_append, List.length_append, hful, hwl, hpl]
    omega
  have hsux : s = u ++ x := by
    have h1 := hs
    have h2 := hx_wp
    rw [h1, h2, List.append_assoc]
  have hperu : Period s u.length := by
    have h1 := hsux
    rw [h1]
    exact Period.of_two_blocks rfl hsplit.symm hwtake
  have hperE : Period s y.length := by
    have h5u : u ++ x = s := by rw [hx_wp, ← List.append_assoc, hs]
    have h5u2 : x ++ p = s := by rw [hs, ← hsplit]
    have h5u3 : u ++ x = x ++ p := h5u.trans h5u2.symm
    have h1 : nCopies y b = p ++ s ++ u := by
      have h2 := hybB
      have h4 := hzA
      calc nCopies y b = (p ++ u) ++ (x ++ u) := by rw [h2, h4]
        _ = p ++ (u ++ (x ++ u)) := List.append_assoc p u (x ++ u)
        _ = p ++ ((u ++ x) ++ u) := congrArg (p ++ ·) (List.append_assoc u x u).symm
        _ = (p ++ (u ++ x)) ++ u := (List.append_assoc p (u ++ x) u).symm
        _ = (p ++ (x ++ p)) ++ u := congrArg (fun t => (p ++ t) ++ u) h5u3
        _ = (p ++ s) ++ u := congrArg (fun t => (p ++ t) ++ u) h5u2
    have h2 : Period (nCopies y b) y.length := nCopies_period y b hy (by omega)
    have h5 : (nCopies y b).drop p.length = s ++ u := by
      rw [h1, List.append_assoc, drop_append_length]
    have h4 : Period ((nCopies y b).drop p.length) y.length := Period.to_drop h2
    have h6 : Period (s ++ u) y.length := by rw [← h5]; exact h4
    have h7 : Period ((s ++ u).take s.length) y.length := Period.prefix h6 (by simp [List.length_append])
    simpa using h7
  -- (7) Fine–Wilf on the critical word
  set g := Nat.gcd u.length y.length with hg
  have hupos0 : 0 < u.length := by rw [hful]; exact hfu
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) hupos0
  have hfw : u.length + y.length - Nat.gcd u.length y.length ≤ s.length := by
    have h1 : u.length + y.length ≤ s.length := by
      have h3 := hslen
      have h4 := hed
      omega
    have h2 : u.length + y.length - Nat.gcd u.length y.length ≤ u.length + y.length := by omega
    exact h2.trans h1
  have hperg : Period s g := by
    have h1 := hperu
    have h2 := hperE
    have h3 := hg
    exact h1.fineWilf h2 hfw
  have hgdivU : g ∣ u.length := by simpa [hg] using (Nat.gcd_dvd_left u.length y.length)
  have hgdivE : g ∣ y.length := by simpa [hg] using (Nat.gcd_dvd_right u.length y.length)
  have hbe_len : b * y.length = 2 * u.length + z.length := by
    have h1 := hlen
    have h2 := hful
    omega
  have hgdivZ : g ∣ z.length := by
    have h1 : g ∣ b * y.length := dvd_trans hgdivE (Nat.dvd_mul_left y.length b)
    have h2 : g ∣ 2 * u.length := dvd_trans hgdivU (Nat.dvd_mul_left u.length 2)
    have h3 : g ∣ 2 * u.length + z.length := by rw [← hbe_len]; exact h1
    exact (Nat.dvd_add_iff_right h2).mpr h3
  have hgdivX : g ∣ x.length := by
    have h3 : z.length = u.length + x.length := by have := hful; omega
    have h4 : g ∣ u.length + x.length := by rw [← h3]; exact hgdivZ
    exact (Nat.dvd_add_iff_right hgdivU).mpr h4
  have hgdivW : g ∣ w.length := by
    have h3 : 2 * x.length = z.length + w.length := by have := hwl; omega
    have h4 : g ∣ 2 * x.length := dvd_trans hgdivX (Nat.dvd_mul_left x.length 2)
    have h5 : g ∣ z.length + w.length := by rw [← h3]; exact h4
    exact (Nat.dvd_add_iff_right hgdivZ).mpr h5
  have hgdivP : g ∣ p.length := by
    have h3 : z.length = x.length + p.length := by have := hpl; omega
    have h4 : g ∣ x.length + p.length := by rw [← h3]; exact hgdivZ
    exact (Nat.dvd_add_iff_right hgdivX).mpr h4
  -- (8) the periods of the pieces
  have hperx : Period x g := by
    have h1 := hperg
    have h2 : x = s.drop (s.length - x.length) := by
      have h3 := hsux
      have h5 : (u ++ x).length - x.length = u.length := by
        have h6 : (u ++ x).length = u.length + x.length := List.length_append
        omega
      rw [h3, h5, drop_append_length]
    have h4 : Period (s.drop (s.length - x.length)) g := Period.suffix h1 (by omega)
    exact h2 ▸ h4
  have hperU : Period u g := by
    have h1 := hperg
    have h2 : u = s.take u.length := by
      have h3 := hsux
      have h4 : u = (u ++ x).take u.length := by
        rw [take_append_of_le' (l₁ := u) (l₂ := x) (n := u.length) (by omega),
          show u.length - u.length = 0 by omega, List.take_zero, List.append_nil]
      rw [h3]; exact h4
    have h4 : Period (s.take u.length) g := Period.prefix h1 (by rw [hslen]; omega)
    exact h2 ▸ h4
  have hperW : Period w g := Period.to_drop hperx
  have hperP : Period p g := Period.to_drop hperx
  -- (9) all four pieces are powers of the length-`g` prefix of `x`
  have hupos : 0 < u.length := by rw [hful]; exact hfu
  have hwpos' : 0 < w.length := by rw [hwl]; omega
  have hppos : 0 < p.length := by rw [hpl]; omega
  have hpowX : x = nCopies (x.take g) (x.length / g) :=
    eq_nCopies_of_period_div hgpos hperx hgdivX hx
  have hgleU : g ≤ u.length := dvd_le_of_pos hupos hgdivU
  have hgleW : g ≤ w.length := dvd_le_of_pos hwpos' hgdivW
  have hgleP : g ≤ p.length := dvd_le_of_pos hppos hgdivP
  have hgdivU' : g ∣ z.length - x.length := by rwa [hful] at hgdivU
  have hgdivW' : g ∣ 2 * x.length - z.length := by rwa [hwl] at hgdivW
  have hu_take : u.take g = x.take g := by
    have h1 := hu
    have h2 : g ≤ z.length - x.length := by rwa [hful] at hgleU
    rw [h1]
    exact take_take' h2
  have hlen1 : (z.length - x.length) + g ≤ x.length := by
    have h2 : g ≤ z.length - x.length := by rwa [hful] at hgleU
    omega
  have hlen2 : (2 * x.length - z.length) + g ≤ x.length := by
    have h2 : g ≤ 2 * x.length - z.length := by rwa [hwl] at hgleW
    omega
  have hw_take : w.take g = x.take g := by
    have h1 := hw
    rw [h1]
    exact take_eq_of_mod_period hgpos hperx hgdivU' hlen1
  have hp_take : p.take g = x.take g := by
    have h1 := hp
    rw [h1]
    exact take_eq_of_mod_period hgpos hperx hgdivW' hlen2
  have hpowU : u = nCopies (x.take g) (u.length / g) := by
    have h1 := eq_nCopies_of_period_div hgpos hperU hgdivU (ne_nil_of_length_pos hupos)
    rwa [hu_take] at h1
  have hpowW : w = nCopies (x.take g) (w.length / g) := by
    have h1 := eq_nCopies_of_period_div hgpos hperW hgdivW (ne_nil_of_length_pos hwpos')
    rwa [hw_take] at h1
  have hpowP : p = nCopies (x.take g) (p.length / g) := by
    have h1 := eq_nCopies_of_period_div hgpos hperP hgdivP (ne_nil_of_length_pos hppos)
    rwa [hp_take] at h1
  have hsum1 : u.length / g + (w.length / g + p.length / g) = s.length / g := by
    have h1 : s.length = u.length + w.length + p.length := by
      have h2 := hslen
      have h3 := hful
      have h4 := hwl
      have h5 := hpl
      omega
    have h2 : s.length = g * (s.length / g) := by
      have h7 : g ∣ s.length := by rw [hslen]; exact hgdivZ
      rw [Nat.mul_div_cancel' h7]
    have h3 : (u.length + w.length + p.length) / g
        = u.length / g + (w.length / g + p.length / g) := by
      have hA : (u.length + w.length + p.length) / g
          = (u.length + w.length) / g + p.length / g :=
        dvd_add_div hgpos (Nat.dvd_add hgdivU hgdivW) hgdivP
      have hB : (u.length + w.length) / g = u.length / g + w.length / g :=
        dvd_add_div hgpos hgdivU hgdivW
      rw [hA, hB, Nat.add_assoc]
    have h6 : u.length + w.length + p.length
        = g * (u.length / g + (w.length / g + p.length / g)) := by
      rw [← h3, Nat.mul_div_cancel' (Nat.dvd_add (Nat.dvd_add hgdivU hgdivW) hgdivP)]
    have h7 : s.length = g * (u.length / g + (w.length / g + p.length / g)) := h1.trans h6
    exact (Nat.mul_left_cancel hgpos (h2.symm.trans h7)).symm
  have hpowS : s = nCopies (x.take g) (s.length / g) := by
    have hWP : w ++ p = nCopies (x.take g) (w.length / g) ++ nCopies (x.take g) (p.length / g) :=
      append_congr hpowW hpowP
    have hUP : u ++ (w ++ p) = nCopies (x.take g) (u.length / g)
        ++ (nCopies (x.take g) (w.length / g) ++ nCopies (x.take g) (p.length / g)) :=
      append_congr hpowU hWP
    calc s = u ++ w ++ p := hs
      _ = u ++ (w ++ p) := List.append_assoc u w p
      _ = nCopies (x.take g) (u.length / g)
          ++ (nCopies (x.take g) (w.length / g) ++ nCopies (x.take g) (p.length / g)) := hUP
      _ = nCopies (x.take g) (u.length / g + (w.length / g + p.length / g)) := by
        rw [nCopies_add, nCopies_add]
      _ = nCopies (x.take g) (s.length / g) := by rw [hsum1]
  have hpowZ : z = nCopies (x.take g) (z.length / g) := by
    have h1 : z.length = x.length + u.length := by have := hful; omega
    calc z = x ++ u := hzA
      _ = nCopies (x.take g) (x.length / g) ++ nCopies (x.take g) (u.length / g) :=
        append_congr hpowX hpowU
      _ = nCopies (x.take g) ((x.length + u.length) / g) := by
        rw [(nCopies_add (x.take g) (x.length / g) (u.length / g)).symm,
          dvd_add_div hgpos hgdivX hgdivU]
      _ = nCopies (x.take g) (z.length / g) := by
        rw [h1, dvd_add_div hgpos hgdivX hgdivU]
  have hbe2 : b * y.length = p.length + u.length + z.length := by
    have h1 := hybB
    have h2 := congrArg List.length h1
    rw [nCopies_length, List.length_append, List.length_append] at h2
    exact h2
  have hdiv3 : (p.length + u.length + z.length) / g
      = p.length / g + u.length / g + z.length / g := by
    have hA : (p.length + u.length + z.length) / g
        = (p.length + u.length) / g + z.length / g :=
      dvd_add_div hgpos (Nat.dvd_add hgdivP hgdivU) hgdivZ
    have hB : (p.length + u.length) / g = p.length / g + u.length / g :=
      dvd_add_div hgpos hgdivP hgdivU
    rw [hA, hB]
  have hPU : p ++ u = nCopies (x.take g) (p.length / g) ++ nCopies (x.take g) (u.length / g) :=
    append_congr hpowP hpowU
  have hybB' : nCopies y b = (nCopies (x.take g) (p.length / g)
      ++ nCopies (x.take g) (u.length / g)) ++ nCopies (x.take g) (z.length / g) := by
    refine hybB.trans ?_
    exact append_congr hPU hpowZ
  have hpowY : nCopies y b = nCopies (x.take g) (b * y.length / g) := by
    rw [hybB', ← nCopies_add, ← nCopies_add, ← hdiv3, hbe2]
  -- (10) conclusion
  have hgleX : g ≤ x.length := dvd_le_of_pos hxpos hgdivX
  have hxtakepos : 0 < (x.take g).length := by
    rw [List.length_take_of_le hgleX]
    exact hgpos
  have hgt : 0 < b * y.length / g := by
    have h7 : g ∣ b * y.length := dvd_trans hgdivE (Nat.dvd_mul_left y.length b)
    exact Nat.div_pos (by omega) hgpos
  obtain ⟨r, hr, i, j, hi, hj, hyR, hqR⟩ :=
    eqPow_commonRoot (x := y) (w := x.take g) (p := b * y.length / g) (m := b) hy
      (ne_nil_of_length_pos hxtakepos) (by omega) (Nat.succ_le_of_lt hgt) hpowY
  have h1 : x = nCopies r (j * (x.length / g)) := by
    calc x = nCopies (x.take g) (x.length / g) := hpowX
      _ = nCopies (nCopies r j) (x.length / g) :=
        congrArg (fun w => nCopies w (x.length / g)) hqR
      _ = nCopies r (j * (x.length / g)) := nCopies_compose r j (x.length / g)
  have hxy : x ++ y = nCopies r (j * (x.length / g) + i) := by
    calc x ++ y = nCopies r (j * (x.length / g)) ++ nCopies r i := append_congr h1 hyR
      _ = nCopies r (j * (x.length / g) + i) :=
        (nCopies_add r (j * (x.length / g)) i).symm
  have hyx : y ++ x = nCopies r (i + j * (x.length / g)) := by
    calc y ++ x = nCopies r i ++ nCopies r (j * (x.length / g)) := append_congr hyR h1
      _ = nCopies r (i + j * (x.length / g)) := (nCopies_add r i (j * (x.length / g))).symm
  rw [hxy, hyx, Nat.add_comm]
end AssemblyP1