import Mathlib.Data.Nat.ModEq
import AssemblyP1.WordPeriodicity

/-!
# Primitivity of `A^m ++ B^m`: the Fine–Wilf consequence needed by the branching construction

This module continues the `A^m B^m` line started in
`AssemblyP1/WordPeriodicity` (issue #92). It proves, from the Fine–Wilf theorem
kernel-checked in that module and elementary list lemmas only, the exact
periodicity/commutation consequence that the branching construction of
`docs/scalar-primitive-spellings-83.md` needs.

## Main results

* `commuting_commonRoot` — two commuting nonempty words are powers of a common
  nonempty word (classical commutation lemma, derived here from Fine–Wilf).
* `pow_pow_commonRoot` — if `x^e = y^f` with `e, f >= 2` then `x` and `y` are
  powers of a common nonempty word. (The two-unknown part of the classical
  Lyndon–Schützenberger statement.)
* `ampbmp_commonRoot` — **the main theorem**: for nonempty `x, y` with
  `a, b >= 2`, `c >= 1`, if `x^a ++ y^b = z^c` and `(a-1)*|x| >= |z|` then
  `x`, `y`, `z` are powers of one common nonempty word. This is exactly the
  "case solved by the periodicity lemma" of the classical proof of
  `x^a y^b = z^c`.
* `ampbmp_head_eq_of_pow` — the separator consequence. If
  `A^m ++ B^m = U^k` with `m, k >= 2`, `A, B` nonempty and `(m-1)*|A| >= |U|`,
  then `A` and `B` start with the same letter. This is the step the graph
  argument uses: cutting a cyclic Eulerian spelling at two visits to a vertex
  with two distinct outgoing edge types produces two closed excursions with
  *different* first edge types, i.e. different first letters.
* `ampbmp_not_properPower_of_head_ne`, `ampbmp_primitive_of_head_ne` —
  primitivity of `A^m ++ B^m` from the separator condition plus that
  quantitative hypothesis.
* `dvd_mul_letterCount_of_pow`, `dvd_mul_of_letterCount_eq_one` — the
  graph-side divisibility step: in a witness `A^m ++ B^m = U^k` the exponent
  `k` divides `m` times the number of occurrences of every letter in `A ++ B`;
  in particular, if some letter occurs exactly once in `A ++ B` (a special case
  of the `gcd(c_0) = 1` hypothesis of the scalar-ray theorem), then `k | m`.
  Together with `k >= 2` this restricts the possible witnesses to proper
  divisors of `m`.
* `ampbmp_no_pow_four_example` — a small worked instance.

## What is *not* proved here

The unconditional statement "nonempty `A, B` with distinct first letters have
`A^m ++ B^m` primitive for every `m >= 2`" is the full classical
Lyndon–Schützenberger theorem for `x^a y^b = z^c` with `a, b, c >= 2`. The two
"easy" cases are settled above by Fine–Wilf; the remaining core cases of the
classical proof (`c = 3` with a specific `u, v, w` decomposition, and `c = 2`
with an induction on `|z|`) are **not** formalised here. Concretely, the
hypothesis `(m-1)*|A| >= |U|` fails for a witness `A^m ++ B^m = U^k` whenever
`|U| = m(|A|+|B|)/k` is larger than `(m-1)*|A|`; since `|A| <= max(|A|,|B|)`,
this happens in particular for every *square* witness `k = 2` with
`|A| = |B|`, and more generally whenever the two excursions have nearly equal
length. See `docs/amp-bmp-primitive-92.md` for the exact residual statement.

No `sorry`, no `admit`, no new axioms.
-/

namespace AssemblyP1

open List

variable {α : Type _}

/-! ## Repetition of a word -/

/-- `nCopies l k` is the concatenation of `k` copies of the word `l`:
`nCopies l 0 = []` and `nCopies l (k+1) = l ++ nCopies l k`. -/
def nCopies (l : List α) : ℕ → List α
  | 0 => []
  | k + 1 => l ++ nCopies l k

@[simp] theorem nCopies_zero (l : List α) : nCopies l 0 = [] := rfl

theorem nCopies_succ (l : List α) (k : ℕ) : nCopies l (k + 1) = l ++ nCopies l k := rfl

/-- A positive divisor of a positive number does not exceed it. -/
theorem dvd_le_of_pos {d n : ℕ} (hn : 0 < n) (h : d ∣ n) : d ≤ n :=
  Nat.le_of_dvd hn h

theorem length_pos_of_ne_nil {l : List α} (h : l ≠ []) : 0 < l.length := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => simp

theorem ne_nil_of_length_pos {l : List α} (h : 0 < l.length) : l ≠ [] := by
  cases l with
  | nil => simp at h
  | cons a t => exact List.cons_ne_nil a t

theorem nCopies_length (l : List α) (k : ℕ) : (nCopies l k).length = k * l.length := by
  induction k with
  | zero => simp [nCopies_zero]
  | succ k ih => rw [nCopies_succ, List.length_append, ih, Nat.succ_mul]; omega

theorem nCopies_add (l : List α) (a b : ℕ) : nCopies l (a + b) = nCopies l a ++ nCopies l b := by
  induction a with
  | zero => simp
  | succ a ih => rw [show a + 1 + b = (a + b) + 1 by omega, nCopies_succ, ih, ← List.append_assoc,
    nCopies_succ]

theorem nCopies_compose (l : List α) (p q : ℕ) :
    nCopies (nCopies l p) q = nCopies l (p * q) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [nCopies_succ, ih, ← nCopies_add, Nat.mul_add, Nat.mul_one]
      have h2 : p + p * q = p * q + p := by omega
      rw [h2]

theorem length_le_nCopies_length {l : List α} {k : ℕ} (hk : 1 ≤ k) :
    l.length ≤ (nCopies l k).length := by
  rw [nCopies_length]
  simpa using Nat.mul_le_mul_right l.length hk

theorem nCopies_pos_length {l : List α} {k : ℕ} (hl : l ≠ []) (hk : 1 ≤ k) :
    0 < (nCopies l k).length := by
  have h1 : 0 < l.length := length_pos_of_ne_nil hl
  rw [nCopies_length]
  exact Nat.mul_pos (by omega) h1

theorem ne_nil_nCopies {l : List α} {k : ℕ} (hl : l ≠ []) (hk : 1 ≤ k) : nCopies l k ≠ [] := by
  exact ne_nil_of_length_pos (nCopies_pos_length hl hk)

/-- Elementary modular arithmetic facts used to compare indices. -/
theorem mod_add_self (m i : ℕ) : (i + m) % m = i % m := by
  exact Nat.add_mod_right i m

theorem mod_sub_self (m i : ℕ) (h : m ≤ i) : (i - m) % m = i % m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rw [hm]; rfl
  have h1 : (i - m) ≡ i [MOD m] :=
    (Nat.modEq_iff_dvd' (n := m) (a := i - m) (b := i) (by omega)).mpr (by
      have h2 : i - (i - m) = m := by omega
      rw [h2])
  exact Nat.mod_eq_of_modEq (h1.trans (Nat.ModEq.symm (Nat.mod_modEq i m)))
    (Nat.mod_lt (x := i) (y := m) hm)

/-- The letter at index `i` of a repetition of `k` copies of `l` is the letter of
`l` at index `i mod |l|`. This is the index-level reason why `|l|` is a period of
`l^k`, and it is the only combinatorial input used below. -/
theorem nCopies_getElem?_aux (l : List α) : ∀ (k i : ℕ), i < (nCopies l k).length →
    (nCopies l k)[i]? = l[i % l.length]? := by
  intro k
  induction k with
  | zero => intro i hi; simp at hi
  | succ k ih =>
    intro i hi
    have hlen : (nCopies l (k + 1)).length = l.length + (nCopies l k).length := by
      rw [nCopies_succ, List.length_append]
    rw [nCopies_succ, List.getElem?_append]
    by_cases h1 : i < l.length
    · simp only [ite_eq_left h1, Nat.mod_eq_of_lt h1]
    · simp only [ite_eq_right h1]
      have h3 : i - l.length < (nCopies l k).length := by omega
      rw [ih (i - l.length) h3]
      congr 1
      exact mod_sub_self l.length i (Nat.le_of_not_gt h1)

theorem nCopies_getElem? {l : List α} {k i : ℕ} (hi : i < (nCopies l k).length) :
    (nCopies l k)[i]? = l[i % l.length]? := nCopies_getElem?_aux l k i hi

/-- `|l|` is a period of `l^k` whenever `l` is nonempty and `k >= 1`. -/
theorem nCopies_period (l : List α) (k : ℕ) (_hl : l ≠ []) (_hk : 1 ≤ k) :
    Period (nCopies l k) l.length := by
  intro i hi
  have h1 : i < (nCopies l k).length := by omega
  have h2 : i + l.length < (nCopies l k).length := hi
  rw [nCopies_getElem? h1, nCopies_getElem? h2]
  congr 1
  exact (mod_add_self l.length i).symm

/-- A `d`-periodic word whose length is a multiple of `d` is a repetition of its
length-`d` prefix. This is the bridge from a Fine–Wilf gcd-period to the
"powers of a common word" conclusion. -/
theorem eq_nCopies_of_period_div {w : List α} {d : ℕ} (hd : 0 < d) (per : Period w d)
    (hdiv : d ∣ w.length) (hw : w ≠ []) : w = nCopies (w.take d) (w.length / d) := by
  have hpos : 0 < w.length := length_pos_of_ne_nil hw
  have hle : d ≤ w.length := Nat.le_of_dvd hpos hdiv
  have htlen : (w.take d).length = d := by rw [List.length_take, Nat.min_eq_left hle]
  have hdiv' : w.length / d * d = w.length := Nat.div_mul_cancel hdiv
  apply List.ext_getElem?
  intro i
  by_cases hi : i < w.length
  · have hi2 : i < (nCopies (w.take d) (w.length / d)).length := by
      rw [nCopies_length, htlen, hdiv']; omega
    have hmod : (w.take d)[i % (w.take d).length]? = w[i % d]? := by
      rw [List.getElem?_take, htlen]
      simp only [Nat.mod_lt (x := i) (y := d) hd, ↓reduceIte,
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le (Nat.mod_lt (x := i) (y := d) hd) hle)]
    rw [List.getElem?_eq_getElem hi, nCopies_getElem? hi2, hmod]
    exact (List.getElem?_eq_getElem hi).symm.trans (per.of_mod hd i hi)
  · have hi2 : (nCopies (w.take d) (w.length / d)).length ≤ i := by
      rw [nCopies_length, htlen, hdiv']; omega
    rw [List.getElem?_eq_none_iff.mpr hi2, List.getElem?_eq_none_iff.mpr (by omega)]

/-- Periods restrict to prefixes. -/
theorem Period.prefix {w : List α} {d : ℕ} (per : Period w d) {T : ℕ} (hT : T ≤ w.length) :
    Period (w.take T) d := by
  have hlenT : (w.take T).length = T := List.length_take.trans (Nat.min_eq_left hT)
  intro i hi
  rw [hlenT] at hi
  have h2 : i + d < w.length := by omega
  rw [List.getElem?_take, ite_eq_left (by omega : i < T)]
  rw [List.getElem?_take, ite_eq_left (by omega : i + d < T)]
  exact per i h2

/-- Converse bridge: if every letter of `w` is the letter of `w.take d` at the
residue `i mod d`, and `d` divides `|w|`, then `w` is a repetition of `w.take d`.
This is the index-level form of "a word determined by its residues mod `d` is a
repetition of its `d`-block". -/
theorem eq_nCopies_of_mod {w : List α} {d : ℕ} (hd : 0 < d) (hdiv : d ∣ w.length)
    (h : ∀ i, i < w.length → w[i]? = (w.take d)[i % d]?) :
    w = nCopies (w.take d) (w.length / d) := by
  cases w with
  | nil => simp [nCopies_zero]
  | cons a t =>
    have hwpos : 0 < (a :: t).length := by simp
    have hle : d ≤ (a :: t).length := dvd_le_of_pos hwpos hdiv
    have htlen : ((a :: t).take d).length = d := by
      rw [List.length_take, Nat.min_eq_left hle]
    have hdiv' : (a :: t).length / d * d = (a :: t).length := Nat.div_mul_cancel hdiv
    apply List.ext_getElem?
    intro i
    by_cases hi : i < (a :: t).length
    · have hi2 : i < (nCopies ((a :: t).take d) ((a :: t).length / d)).length := by
        rw [nCopies_length, htlen, hdiv']; omega
      rw [nCopies_getElem? hi2, List.getElem?_take, htlen]
      simp only [Nat.mod_lt (x := i) (y := d) hd, ↓reduceIte]
      have h2 := h i hi
      rw [h2]
      rw [List.getElem?_take]
      exact ite_eq_left (Nat.mod_lt (x := i) (y := d) hd)
    · have hi2 : (nCopies ((a :: t).take d) ((a :: t).length / d)).length ≤ i := by
        rw [nCopies_length, htlen, hdiv']; omega
      rw [List.getElem?_eq_none_iff.mpr hi2,
        List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hi)]

/-- A word with period `p`, whose first `T` letters are determined by their residues
mod `d` (with `d` dividing `p` and `d <= T`), is itself determined by residues mod `d`. -/
theorem eq_nCopies_of_period_prefix {w : List α} {p d T : ℕ} (hp : 0 < p) (per : Period w p)
    (hdp : d ∣ p) (hd : 0 < d) (hpd : p ≤ T) (_hTle : T ≤ w.length)
    (hmod : ∀ i, i < T → w[i]? = w[i % d]?) (hdw : d ∣ w.length) :
    w = nCopies (w.take d) (w.length / d) := by
  refine eq_nCopies_of_mod hd hdw ?_
  intro i hi
  have h1 := per.of_mod hp i hi
  have hmp : i % p < p := Nat.mod_lt (x := i) (y := p) hp
  have h2 : i % p < T := Nat.lt_of_lt_of_le hmp hpd
  have h4 := hmod (i % p) h2
  have h6 : (i % p) % d = i % d := by
    refine Nat.mod_eq_of_modEq
      (Nat.ModEq.trans (Nat.ModEq.of_dvd hdp (Nat.mod_modEq i p))
        (Nat.ModEq.symm (Nat.mod_modEq i d)))
      (Nat.mod_lt (x := i) (y := d) hd)
  have h5 : w[i % p]? = w[i % d]? := by
    rw [h4, h6]
  rw [h1, h5, List.getElem?_take, ite_eq_left (Nat.mod_lt (x := i) (y := d) hd)]

/-- A `d`-period of a word passes to any word equal to one of its prefixes. -/
theorem Period.eq_of_take {w v : List α} {d : ℕ} (per : Period w d) {T : ℕ} (hT : T ≤ w.length)
    (hv : w.take T = v) : Period v d := by
  have h1 : Period (w.take T) d := per.prefix hT
  rw [hv] at h1
  exact h1

/-- Periods restrict to tails (`drop`), hence to suffixes of a prescribed length. -/
theorem Period.to_drop {w : List α} {d s : ℕ} (per : Period w d) : Period (w.drop s) d := by
  intro i hi
  have hlen : (w.drop s).length = w.length - s := List.length_drop
  rw [hlen] at hi
  rw [List.getElem?_drop, List.getElem?_drop]
  simpa only [Nat.add_assoc] using per (s + i) (by omega)

/-- Periods restrict to suffixes of a prescribed length. -/
theorem Period.suffix {w : List α} {d : ℕ} (per : Period w d) {T : ℕ} (_hT : T ≤ w.length) :
    Period (w.drop (w.length - T)) d :=
  Period.to_drop per

/-- Dropping a prefix of a concatenation leaves the tail. -/
theorem drop_append_length (l₁ l₂ : List α) : (l₁ ++ l₂).drop l₁.length = l₂ := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop, List.getElem?_append, ite_eq_right (by omega)]
  by_cases h2 : i < l₂.length
  · have h3 : l₁.length + i - l₁.length = i := by omega
    rw [h3, List.getElem?_eq_getElem h2]
  · rw [List.getElem?_eq_none_iff.mpr (by omega), List.getElem?_eq_none_iff.mpr (by omega)]

/-- The letters of a concatenation that lie in the first block are those of the first
block. -/
theorem getElem?_append_left {l₁ l₂ : List α} {i : ℕ} (hi : i < l₁.length) :
    (l₁ ++ l₂)[i]? = l₁[i]? := by
  rw [List.getElem?_append, ite_eq_left hi]

/-- Taking a prefix of a concatenation that fits inside the first block agrees with
taking it from the first block alone. -/
theorem take_append_of_le (l₁ l₂ : List α) {n : ℕ} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).take n = l₁.take n := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_take]
  by_cases h2 : i < n
  · rw [ite_eq_left h2, List.getElem?_append, ite_eq_left (by omega), ite_eq_left h2]
  · rw [ite_eq_right h2, ite_eq_right h2]

/-- The prefix of a concatenation of length of the first block is that block. -/
theorem take_append_length (l₁ l₂ : List α) : (l₁ ++ l₂).take l₁.length = l₁ := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take]
  by_cases h : i < l₁.length
  · rw [ite_eq_left h, List.getElem?_append, ite_eq_left (by omega)]
  · rw [ite_eq_right h]
    exact (List.getElem?_eq_none_iff.mpr (by omega)).symm

/-- `take` of a prefix of length at most the original length. -/
theorem take_take' {w : List α} {i j : ℕ} (h : i ≤ j) : (w.take j).take i = w.take i := by
  rw [take_take, Nat.min_eq_left h]

/-- Indexing inside `l^a ++ rest`: for `i < a * |l|` the letter is that of `l` at
index `i mod |l|`. -/
theorem getElem?_nCopies_append_lt (l rest : List α) : ∀ (a i : ℕ), 1 ≤ a →
    i < a * l.length → (nCopies l a ++ rest)[i]? = l[i % l.length]? := by
  intro a
  induction a with
  | zero => intro i h1 h2; omega
  | succ k ih =>
    intro i h1 h2
    have hsplit : nCopies l (k + 1) ++ rest = l ++ (nCopies l k ++ rest) := by
      rw [nCopies_succ, List.append_assoc]
    rw [hsplit, List.getElem?_append]
    by_cases h3 : i < l.length
    · rw [ite_eq_left h3, Nat.mod_eq_of_lt h3]
    · rw [ite_eq_right h3]
      by_cases hk : 1 ≤ k
      · have h4 : i - l.length < k * l.length := by
          simp only [Nat.succ_mul] at h2
          omega
        rw [ih (i - l.length) hk h4]
        congr 1
        rw [mod_sub_self l.length i (Nat.le_of_not_gt h3)]
      · have hk0 : k = 0 := by omega
        subst hk0
        simp only [Nat.succ_mul, Nat.zero_mul] at h2
        omega

/-- The prefix of length `|l|` of a word starting with `a >= 1` copies of `l` is `l`. -/
theorem take_nCopies_append (l rest : List α) (a : ℕ) (h1 : 1 ≤ a) :
    (nCopies l a ++ rest).take l.length = l := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take]
  by_cases h2 : i < l.length
  · have h3 : i < a * l.length := by
      have h4 := length_le_nCopies_length (l := l) (k := a) h1
      rw [nCopies_length] at h4
      omega
    rw [ite_eq_left h2, getElem?_nCopies_append_lt l rest a i h1 h3, Nat.mod_eq_of_lt h2,
      List.getElem?_eq_getElem h2]
  · rw [ite_eq_right h2]
    exact (List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt h2)).symm

/-- If `w = l^a ++ rest` with `a >= 1`, then `w`'s prefix of length `a * |l|` is `l^a`. -/
theorem take_nCopies_append_length (l rest : List α) (a : ℕ) (h1 : 1 ≤ a) :
    (nCopies l a ++ rest).take (a * l.length) = nCopies l a := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take]
  by_cases h2 : i < a * l.length
  · have h3 : i < (nCopies l a).length := by rw [nCopies_length]; exact h2
    have hlp : 0 < l.length := by
      rcases Nat.eq_zero_or_pos l.length with hc | hc
      · rw [hc] at h2
        exact absurd h2 (by simp)
      · exact hc
    rw [ite_eq_left h2, getElem?_nCopies_append_lt l rest a i h1 h2, nCopies_getElem? h3,
      List.getElem?_eq_getElem (Nat.mod_lt (x := i) (y := l.length) hlp)]
  · rw [ite_eq_right h2]
    exact (List.getElem?_eq_none_iff.mpr (by rw [nCopies_length]; omega)).symm

/-- The prefix of a nonempty repetition of length `|l|` is `l`. -/
theorem take_nCopies (l : List α) (k : ℕ) (hk : 1 ≤ k) : (nCopies l k).take l.length = l := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hk
  subst hr
  rw [Nat.add_comm, nCopies_succ, take_append_length]

/-- The tail of `l^k` of length `m * |l|` (for `m <= k`) is `l^m`. -/
theorem nCopies_suffix (l : List α) (k m : ℕ) (hm : m ≤ k) :
    (nCopies l k).drop (k * l.length - m * l.length) = nCopies l m := by
  have hle : m * l.length ≤ k * l.length := Nat.mul_le_mul_right _ hm
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop]
  by_cases hi : i < (nCopies l m).length
  · have hmlt : i < m * l.length := hi.trans_eq (nCopies_length l m)
    have hmlpos : 0 < m * l.length := by omega
    have hpos : 0 < l.length := by
      rcases Nat.eq_zero_or_pos l.length with h | h
      · rw [h] at hmlpos; omega
      · exact h
    have hil : k * l.length - m * l.length + i < k * l.length := by
      have h3 : 0 < m * l.length - i := Nat.sub_pos_of_lt hmlt
      have h4 : k * l.length - m * l.length + i = k * l.length - (m * l.length - i) := by
        omega
      rw [h4]
      exact Nat.sub_lt_self h3 (Nat.le_trans (Nat.sub_le _ _) hle)
    have hmod : (k * l.length - m * l.length + i) % l.length = i % l.length := by
      have h1 : k * l.length - m * l.length = (k - m) * l.length := by
        obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hm
        have hsub : k - m = r := by omega
        rw [hr, Nat.add_mul, Nat.add_sub_cancel_left]
        congr 1
        omega
      rw [h1]
      refine Nat.mod_eq_of_modEq (b := i % l.length) ?_ (Nat.mod_lt (x := i) (y := l.length) hpos)
      have h3 : (k - m) * l.length + i ≡ i [MOD l.length] := by
        simpa using
          (Nat.ModEq.add (Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_mul_left l.length (k - m)))
            (Nat.ModEq.refl i))
          (Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_mul_left l.length (k - m))) (Nat.ModEq.refl i)
      exact h3.trans (Nat.ModEq.symm (Nat.mod_modEq i l.length))
    have hmk : (nCopies l k).length = k * l.length := nCopies_length l k
    have hml : (nCopies l m).length = m * l.length := nCopies_length l m
    have hil' : k * l.length - m * l.length + i < (nCopies l k).length := by omega
    rw [nCopies_getElem? hil', hmod, nCopies_getElem? hi]
  · have hmk : (nCopies l k).length = k * l.length := nCopies_length l k
    have hml : (nCopies l m).length = m * l.length := nCopies_length l m
    have h1 : (nCopies l k).length ≤ k * l.length - m * l.length + i := by omega
    have h2 : (nCopies l m).length ≤ i := by omega
    rw [List.getElem?_eq_none_iff.mpr h1, List.getElem?_eq_none_iff.mpr h2]

/-! ## Primitivity -/

/-- `w` is a *nontrivial power*: `w = l^k` for some nonempty `l` and `k >= 2`. -/
def IsProperPower (w : List α) : Prop :=
  ∃ l : List α, l ≠ [] ∧ ∃ k : ℕ, 2 ≤ k ∧ w = nCopies l k

/-- `w` is *primitive*: not a nontrivial power. -/
def IsPrimitive (w : List α) : Prop := ¬ IsProperPower w

/-- Two powers of a common nonempty word concatenate to a proper power. -/
theorem isProperPower_append_commonRoot {x y : List α} {w : List α} {p q : ℕ}
    (hw : w ≠ []) (hp : 1 ≤ p) (hq : 1 ≤ q) (hx : x = nCopies w p) (hy : y = nCopies w q) :
    IsProperPower (x ++ y) := by
  refine ⟨w, hw, p + q, ?_, ?_⟩
  · omega
  · rw [hx, hy, nCopies_add]

/-- The first letter of a nonempty power of a nonempty word is the first letter
of the base word. -/
theorem head_nCopies {w : List α} {k : ℕ} (hw : w ≠ []) (hk : 1 ≤ k) :
    (nCopies w k)[0]? = w[0]? := by
  have h1 : 0 < (nCopies w k).length := nCopies_pos_length hw hk
  rw [nCopies_getElem? h1]
  congr 1

/-- Two nonempty words that are powers of a common nonempty word start with the
same letter. This is the separator step used against the "two distinct outgoing
edge types" hypothesis. -/
theorem head_eq_of_commonRoot {x y : List α} {w : List α} {p q : ℕ}
    (hw : w ≠ []) (hp : 1 ≤ p) (hq : 1 ≤ q) (hx : x = nCopies w p) (hy : y = nCopies w q) :
    x[0]? = y[0]? := by
  rw [hx, hy, head_nCopies hw hp, head_nCopies hw hq]

/-! ## The commutation consequence of Fine–Wilf -/

private theorem period_append_of_comm {x y : List α} (h : x ++ y = y ++ x) (d : ℕ)
    (hd : d = x.length ∨ d = y.length) : Period (x ++ y) d := by
  intro i hi
  rcases hd with rfl | rfl
  · have h1 : i < y.length := by rw [List.length_append] at hi; omega
    have h2 : ¬(i + x.length < x.length) := by omega
    have h3 : i + x.length - x.length = i := by omega
    nth_rewrite 1 [h]
    rw [List.getElem?_append, ite_eq_left h1]
    rw [List.getElem?_append, ite_eq_right h2, h3]
  · have h1 : i < x.length := by rw [List.length_append] at hi; omega
    have h2 : ¬(i + y.length < y.length) := by omega
    have h3 : i + y.length - y.length = i := by omega
    nth_rewrite 2 [h]
    rw [List.getElem?_append, ite_eq_left h1]
    rw [List.getElem?_append, ite_eq_right h2, h3]

/-- **Commutation lemma.** If two nonempty words commute, they are powers of a
common nonempty word. Derived from Fine–Wilf; no Lyndon–Schützenberger
assumption is used. -/
theorem commuting_commonRoot {x y : List α} (hx : x ≠ []) (hy : y ≠ [])
    (h : x ++ y = y ++ x) :
    ∃ w : List α, w ≠ [] ∧ ∃ p q : ℕ, 1 ≤ p ∧ 1 ≤ q ∧ x = nCopies w p ∧ y = nCopies w q := by
  have hxlen : 0 < x.length := length_pos_of_ne_nil hx
  have hylen : 0 < y.length := length_pos_of_ne_nil hy
  set d := Nat.gcd x.length y.length with hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) hxlen
  have hdle : d ≤ x.length := Nat.le_of_dvd hxlen (by simpa [hd] using Nat.gcd_dvd_left _ _)
  have hfw : x.length + y.length - d ≤ (x ++ y).length := by rw [List.length_append]; omega
  have hper : Period (x ++ y) d :=
    (period_append_of_comm h _ (Or.inl rfl)).fineWilf
      (period_append_of_comm h _ (Or.inr rfl)) hfw
  have hperx : Period x d := by
    have h1 := hper.prefix (T := x.length) (by rw [List.length_append]; omega)
    rwa [take_append_length] at h1
  have hpery : Period y d := by
    have h1 := hper.prefix (T := y.length) (by rw [List.length_append]; omega)
    rwa [show (x ++ y).take y.length = y from by
      rw [h, take_append_length]] at h1
  have hxpow : x = nCopies (x.take d) (x.length / d) :=
    eq_nCopies_of_period_div hdpos hperx (by simpa [hd] using Nat.gcd_dvd_left _ _) hx
  have hdle' : d ≤ y.length := Nat.le_of_dvd hylen (by simpa [hd] using Nat.gcd_dvd_right _ _)
  have htake : y.take d = x.take d := by
    have hle : d ≤ (x ++ y).length :=
      Nat.le_trans hdle' (by rw [List.length_append]; omega)
    have hyeq : y = (x ++ y).take y.length := by rw [h, take_append_length y x]
    have hxeq : x = (x ++ y).take x.length := (take_append_length x y).symm
    have h1 : y.take d = (x ++ y).take d := by
      nth_rewrite 1 [hyeq]
      exact take_take' hdle'
    have h2 : x.take d = (x ++ y).take d := by
      nth_rewrite 1 [hxeq]
      exact take_take' hdle
    rw [h1, h2]
  have hypow : y = nCopies (x.take d) (y.length / d) := by
    have := eq_nCopies_of_period_div hdpos hpery (by simpa [hd] using Nat.gcd_dvd_right _ _) hy
    rw [htake] at this
    exact this
  refine ⟨x.take d, ?_, x.length / d, y.length / d, ?_, ?_, hxpow, hypow⟩
  · have : (x.take d).length = d := by rw [List.length_take, Nat.min_eq_left hdle]
    exact ne_nil_of_length_pos (by rw [this]; exact hdpos)
  · exact Nat.div_pos (Nat.le_of_dvd hxlen (by simpa [hd] using Nat.gcd_dvd_left _ _)) hdpos
  · exact Nat.div_pos (Nat.le_of_dvd hylen (by simpa [hd] using Nat.gcd_dvd_right _ _)) hdpos

/-- **Two nontrivial powers that are equal are powers of a common word.** This is
the two-unknown part of the classical Lyndon–Schützenberger statement, and it is
what the three-unknown argument reduces to once a gcd-period has been found. -/
theorem pow_pow_commonRoot {x y : List α} {e f : ℕ} (hx : x ≠ []) (hy : y ≠ [])
    (he : 2 ≤ e) (hf : 2 ≤ f) (h : nCopies x e = nCopies y f) :
    ∃ w : List α, w ≠ [] ∧ ∃ p q : ℕ, 1 ≤ p ∧ 1 ≤ q ∧ x = nCopies w p ∧ y = nCopies w q := by
  have hxlen : 0 < x.length := length_pos_of_ne_nil hx
  have hylen : 0 < y.length := length_pos_of_ne_nil hy
  have h1e : 1 ≤ e := by omega
  have h1f : 1 ≤ f := by omega
  have h2e : 2 ≤ e := he
  have h2f : 2 ≤ f := hf
  have hprod : e * x.length = f * y.length := by
    have h3 := congrArg List.length h
    rwa [nCopies_length, nCopies_length] at h3
  set d := Nat.gcd x.length y.length with hd
  have hfw : x.length + y.length - d ≤ (nCopies x e).length := by
    have hg : d ≤ x.length := Nat.gcd_le_left _ hxlen
    have h3 : x.length + y.length - d ≤ x.length + y.length := by omega
    rw [nCopies_length]
    refine h3.trans ?_
    by_cases hy' : y.length ≤ x.length
    · have h4 : x.length + y.length ≤ 2 * x.length := by omega
      exact h4.trans (Nat.mul_le_mul_right x.length h2e)
    · have h4 : x.length + y.length ≤ 2 * y.length := by omega
      exact (h4.trans (Nat.mul_le_mul_right y.length h2f)).trans_eq hprod.symm
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) hxlen
  have hper : Period (nCopies x e) d := by
    have hper2 : Period (nCopies x e) y.length := by
      rw [h]; exact nCopies_period y f hy h1f
    have h5 := (nCopies_period x e hx h1e).fineWilf hper2 hfw
    rw [← hd] at h5
    exact h5
  have hdivx : d ∣ x.length := by simpa [hd] using (Nat.gcd_dvd_left x.length y.length)
  have hdivy : d ∣ y.length := by simpa [hd] using (Nat.gcd_dvd_right x.length y.length)
  have hdle : d ≤ x.length := dvd_le_of_pos hxlen hdivx
  have hdle' : d ≤ y.length := dvd_le_of_pos hylen hdivy
  have hle : d ≤ (nCopies x e).length := Nat.le_trans hdle (length_le_nCopies_length h1e)
  have hle' : d ≤ (nCopies y f).length := Nat.le_trans hdle' (length_le_nCopies_length h1f)
  have hperx : Period x d := by
    have h1 := hper.prefix (T := x.length) (length_le_nCopies_length h1e)
    rwa [take_nCopies x e h1e] at h1
  have hpery : Period y d := by
    have hly : y.length ≤ (nCopies x e).length := by
      rw [h]; exact length_le_nCopies_length h1f
    have h1 := hper.prefix (T := y.length) hly
    rwa [show (nCopies x e).take y.length = y from by rw [h, take_nCopies y f h1f]] at h1
  have hxpow : x = nCopies (x.take d) (x.length / d) :=
    eq_nCopies_of_period_div hdpos hperx (by simpa [hd] using Nat.gcd_dvd_left _ _) hx
  have htake : y.take d = x.take d := by
    have hyeq : y = (nCopies y f).take y.length := (take_nCopies y f h1f).symm
    have hxeq : x = (nCopies x e).take x.length := (take_nCopies x e h1e).symm
    have h1 : y.take d = (nCopies x e).take d := by
      nth_rewrite 1 [hyeq]
      rw [h, take_take' hdle']
    have h2 : x.take d = (nCopies x e).take d := by
      nth_rewrite 1 [hxeq]
      exact take_take' hdle
    rw [h1, h2]
  have hypow : y = nCopies (x.take d) (y.length / d) := by
    have h3 := eq_nCopies_of_period_div hdpos hpery (by simpa [hd] using Nat.gcd_dvd_right _ _) hy
    rw [htake] at h3
    exact h3
  refine ⟨x.take d, ?_, x.length / d, y.length / d, ?_, ?_, hxpow, hypow⟩
  · have h4 : (x.take d).length = d := by rw [List.length_take, Nat.min_eq_left hdle]
    exact ne_nil_of_length_pos (by rw [h4]; exact hdpos)
  · exact Nat.div_pos hdle hdpos
  · exact Nat.div_pos hdle' hdpos

/-! ## The Fine–Wilf case of `x^a ++ y^b = z^c` -/

/-- **Main theorem of this module.** Let `x, y, z` be words with `x, y` nonempty
and let `a, b >= 2`, `c >= 1`. If

* `x^a ++ y^b = z^c`, and
* `(a - 1) * |x| >= |z|` (equivalently `|z| + |x| <= |x^a|`),

then `x`, `y` and `z` are all powers of one common nonempty word. This is the
"case solved by the periodicity lemma" in the classical proof of the
Lyndon–Schützenberger equation. -/
theorem ampbmp_commonRoot {x y z : List α} {a b c : ℕ}
    (hx : x ≠ []) (hy : y ≠ []) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 1 ≤ c)
    (h : nCopies x a ++ nCopies y b = nCopies z c)
    (hlen : (a - 1) * x.length ≥ z.length) :
    ∃ w : List α, w ≠ [] ∧ ∃ p q r : ℕ, 1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧
      x = nCopies w p ∧ y = nCopies w q ∧ z = nCopies w r := by
  have hxlen : 0 < x.length := length_pos_of_ne_nil hx
  have hylen : 0 < y.length := length_pos_of_ne_nil hy
  have h1a : 1 ≤ a := by omega
  have h1b : 1 ≤ b := by omega
  have hlen' : a * x.length + b * y.length = c * z.length := by
    have h3 := congrArg List.length h
    rwa [List.length_append, nCopies_length, nCopies_length, nCopies_length] at h3
  have hWlen : (nCopies z c).length = a * x.length + b * y.length := by
    rw [nCopies_length]; exact hlen'.symm
  have hzpos : 0 < z.length := by
    cases z with
    | nil =>
      exfalso
      have h5 := hlen'
      simp only [List.length_nil] at h5
      have h4 : 0 < (nCopies x a).length := nCopies_pos_length hx h1a
      rw [nCopies_length] at h4
      omega
    | cons z zs => simp
  set W := nCopies z c with hW
  have hW' : nCopies x a ++ nCopies y b = W := h
  have hWlen' : W.length = a * x.length + b * y.length := by rw [hW] at hWlen; exact hWlen
  have hz : z ≠ [] := ne_nil_of_length_pos hzpos
  have perW0 : Period W z.length := by
    have h1 : W = nCopies z c := by simp [hW]
    rw [h1]; exact nCopies_period z c hz hc
  set d := Nat.gcd x.length z.length with hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) hxlen
  have hdivx : d ∣ x.length := by simpa [hd] using (Nat.gcd_dvd_left x.length z.length)
  have hdivz : d ∣ z.length := by simpa [hd] using (Nat.gcd_dvd_right x.length z.length)
  have hdle : d ≤ x.length := dvd_le_of_pos hxlen hdivx
  have hdle' : d ≤ z.length := dvd_le_of_pos hzpos hdivz
  have hzleW : z.length ≤ W.length := by
    rw [hW]; exact length_le_nCopies_length hc
  -- Fine–Wilf on the prefix `x^a`, which has periods `|x|` and `|z|`
  have hfw : x.length + z.length - d ≤ a * x.length := by
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le h1a
    have h2 : z.length ≤ r * x.length := by
      have h6 := hlen
      rw [hr, show 1 + r - 1 = r from by omega] at h6
      exact h6
    have h3 : a * x.length = x.length + r * x.length := by
      rw [hr, Nat.add_mul, Nat.one_mul]
    have h4 : x.length + z.length - d ≤ x.length + z.length := by omega
    have h5 : x.length + z.length ≤ x.length + r * x.length := by omega
    exact h4.trans (h5.trans_eq h3.symm)
  have hperV : Period (nCopies x a) d := by
    have hv1 : Period (nCopies x a) x.length := nCopies_period x a hx h1a
    have hv2 : Period (nCopies x a) z.length := by
      exact (Period.eq_of_take perW0 (T := a * x.length)) (by rw [hWlen']; omega) (by
        have : (nCopies x a ++ nCopies y b) = W := hW'
        rw [← this]
        exact take_nCopies_append_length x (nCopies y b) a h1a)
    have hfw' : x.length + z.length - Nat.gcd x.length z.length ≤ (nCopies x a).length := by
      simpa [nCopies_length, hd] using hfw
    have h3 := hv1.fineWilf hv2 hfw'
    rw [← hd] at h3
    exact h3
  set w := x.take d with hw
  have hwlen : w.length = d := by rw [hw, List.length_take, Nat.min_eq_left hdle]
  have hwpos : 0 < w.length := by rw [hwlen]; exact hdpos
  have hwne : w ≠ [] := ne_nil_of_length_pos hwpos
  have hperx : Period x d :=
    Period.eq_of_take hperV (T := x.length) (length_le_nCopies_length h1a) (take_nCopies x a h1a)
  have hxpow : x = nCopies w (x.length / d) := by
    have h2 := eq_nCopies_of_period_div (by simpa [hd] using hdpos)
      (hperV.eq_of_take (T := x.length) (length_le_nCopies_length h1a) (take_nCopies x a h1a))
      hdivx hx
    exact h2
  have hwp : 1 ≤ x.length / d := Nat.div_pos hdle hdpos
  -- `z` is a prefix of `W`, so it too is determined by its residues mod `d`, and
  -- `z.take d = x.take d = w`.
  have hleW : d ≤ W.length := by rw [hWlen']; omega
  have hle2 : d ≤ (nCopies x a).length := Nat.le_trans hdle (length_le_nCopies_length h1a)
  have hzpre : W.take z.length = z := by
    rw [hW, take_nCopies z c hc]
  have hzwd0 : z.take d = x.take d := by
    have h1 : z.take d = W.take d := by
      rw [← hzpre, take_take' hdle']
    have h2 : x.take d = W.take d := by
      rw [← hW', take_append_of_le (nCopies x a) (nCopies y b) hle2]
      have h4 : (nCopies x a).take x.length = x := take_nCopies x a h1a
      have h5 : (nCopies x a).take d = ((nCopies x a).take x.length).take d := by
        symm
        exact take_take' hdle
      rw [h5, h4]
    rw [h1, ← h2]
  have hWd : W.take d = w := by
    have h1 : (nCopies x a ++ nCopies y b).take d = (nCopies x a).take d := by
      rw [take_append_of_le (nCopies x a) (nCopies y b) hle2]
    have h2 : (nCopies x a).take d = x.take d := by
      have h3 : (nCopies x a).take d = ((nCopies x a).take x.length).take d := by
        symm
        exact take_take' hdle
      rw [h3, take_nCopies x a h1a]
    rw [← hW', h1, h2, hw]
  have hzwd : z.take d = w := by rw [hzwd0, hw]
  -- `W.take d = x.take d = w`, and the letters of `W` are determined by their
  -- residues mod `d`; `z` sits inside the first block, so the same holds for `z`.
  have hVeqW : ∀ i, i < (nCopies x a).length → (nCopies x a)[i]? = W[i]? := by
    intro i hi
    have h := congrArg (fun l : List α => l[i]?) hW'.symm
    rw [getElem?_append_left hi] at h
    exact h.symm
  have hperVmod : ∀ i, i < (nCopies x a).length → (nCopies x a)[i]? = W[i % d]? := by
    intro i hi
    have h4 := hperV.of_mod (by simpa [hd] using hdpos) i hi
    have hmod : i % d < d := Nat.mod_lt (x := i) (y := d) (by simpa [hd] using hdpos)
    have h9 : (nCopies x a)[i % d]? = W[i % d]? :=
      hVeqW (i % d) (by
        have := hle2
        omega)
    rw [h9] at h4
    exact h4
  have hzleV : z.length ≤ (nCopies x a).length := by
    rw [nCopies_length]
    have h5 := hlen
    have h6 : z.length ≤ a * x.length := by omega
    omega
  have hVleW : (nCopies x a).length ≤ W.length := by
    rw [hWlen', nCopies_length]
    omega
  have hWmodV : ∀ i, i < (nCopies x a).length → W[i]? = W[i % d]? := by
    intro i hi
    exact (hVeqW i hi).symm.trans (hperVmod i hi)
  have hdzc : d ∣ c * z.length := by
    refine Nat.dvd_trans hdivz ?_
    rw [Nat.mul_comm]
    exact Nat.dvd_mul_right z.length c
  have hdzW : d ∣ W.length := by
    show d ∣ (nCopies z c).length
    rw [nCopies_length]
    exact hdzc
  have hWpow : W = nCopies w (W.length / d) := by
    have h1 : W = nCopies (W.take d) (W.length / d) :=
      eq_nCopies_of_period_prefix (w := W) (p := z.length) (d := d)
        (T := (nCopies x a).length) hzpos perW0 hdivz hdpos hzleV hVleW hWmodV hdzW
    have h2 := h1
    rw [hWd] at h2
    exact h2
  have hk1 : W.length / d * w.length = W.length := by
    rw [hwlen]
    exact Nat.div_mul_cancel hdzW
  have hWmodw : ∀ i, i < W.length → W[i]? = w[i % d]? := by
    intro i hi
    have h2 : (nCopies w (W.length / d)).length = W.length := by rw [nCopies_length, hk1]
    have h1 := congrArg (fun l : List α => l[i]?) hWpow
    have h3 : i < (nCopies w (W.length / d)).length := by rw [h2]; exact hi
    have h4 := nCopies_getElem?_aux w (W.length / d) i h3
    exact h1.trans (h4.trans (by rw [hwlen]))
  have hzmod : ∀ i, i < z.length → z[i]? = (z.take d)[i % d]? := by
    intro i hi
    have h0 : z[i]? = W[i]? := by
      have hh := congrArg (fun l : List α => l[i]?) hzpre
      rw [List.getElem?_take, ite_eq_left hi] at hh
      exact hh.symm
    have h1 := hVeqW i (by have := hzleV; omega)
    have h2 := hWmodV i (by have := hzleV; omega)
    have hmodlt : i % d < d := Nat.mod_lt (x := i) (y := d) (by simpa [hd] using hdpos)
    have h3 := hWmodw (i % d) (Nat.lt_of_lt_of_le hmodlt hleW)
    rw [Nat.mod_mod] at h3
    calc z[i]? = W[i]? := h0
      _ = W[i % d]? := h2
      _ = w[i % d]? := h3
      _ = (z.take d)[i % d]? := hzwd.symm ▸ rfl
  have hzpow : z = nCopies w (z.length / d) := by
    have h1 : z = nCopies (z.take d) (z.length / d) := eq_nCopies_of_mod hdpos hdivz hzmod
    rw [hzwd] at h1
    exact h1
  -- `y^b` is the tail of `W` of length `b * |y|`, hence also a repetition of `w`
  have hdby : d ∣ b * y.length := by
    have h1 : d ∣ a * x.length + b * y.length := by
      have h5 := hdzc
      rwa [← hlen'] at h5
    have h2 : d ∣ a * x.length := Nat.dvd_mul_left_of_dvd hdivx a
    have h5 : d ∣ b * y.length ↔ d ∣ a * x.length + b * y.length := Nat.dvd_add_iff_right h2
    exact h5.mpr h1
  have hsd : b * y.length / d * w.length = b * y.length := by
    rw [hwlen]
    exact Nat.div_mul_cancel hdby
  have hidx : W.length / d * w.length - b * y.length / d * w.length = a * x.length := by
    rw [hk1, hsd]
    have := hWlen'
    omega
  have hle : b * y.length / d ≤ W.length / d := by
    have h3 : b * y.length / d * d ≤ W.length := by
      rw [Nat.div_mul_cancel hdby]
      have h4 : b * y.length ≤ W.length := by
        have := hWlen'
        omega
      exact h4
    exact (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr h3
  have hys : nCopies y b = nCopies w (b * y.length / d) := by
    have htail : nCopies y b = (nCopies w (W.length / d)).drop (a * x.length) := by
      have h2 := drop_append_length (nCopies x a) (nCopies y b)
      have h4 : (nCopies x a).length = a * x.length := nCopies_length x a
      rw [h4] at h2
      have h3 := congrArg (fun l : List α => l.drop (a * x.length)) hW'
      rw [h2] at h3
      have h5 := congrArg (fun l : List α => l.drop (a * x.length)) hWpow
      exact h3.trans h5
    calc nCopies y b = (nCopies w (W.length / d)).drop (a * x.length) := htail
      _ = (nCopies w (W.length / d)).drop
          (W.length / d * w.length - b * y.length / d * w.length) := by rw [hidx]
      _ = nCopies w (b * y.length / d) :=
        nCopies_suffix w (W.length / d) (b * y.length / d) hle
  -- The tail `y^b` is a power of `w`; if that power is a single copy of `w`, then `w`
  -- itself is a power of `y`, otherwise `y` and `w` share a common root.
  have hzp : 1 ≤ z.length / d := Nat.div_pos hdle' hdpos
  have hm1 : 1 ≤ b * y.length / d := by
    exact (Nat.le_div_iff_mul_le hdpos).mpr (Nat.le_of_dvd (Nat.mul_pos h1b hylen) (by simpa using hdby))
  rcases Nat.lt_or_ge (b * y.length / d) 2 with hlt | hge
  · have h1 : b * y.length / d = 1 := by omega
    have hys' : nCopies y b = nCopies w 1 := by rw [hys, h1]
    have hweq : w = nCopies y b := by
      have h2 := hys'.symm
      rw [nCopies_succ, nCopies_zero] at h2
      simpa using h2
    have hmul : 1 ≤ b * (x.length / d) := by
      calc 1 ≤ x.length / d := hwp
        _ ≤ b * (x.length / d) := Nat.le_mul_of_pos_left _ h1b
    have hmulz : 1 ≤ b * (z.length / d) := by
      calc 1 ≤ z.length / d := hzp
        _ ≤ b * (z.length / d) := Nat.le_mul_of_pos_left _ h1b
    refine ⟨y, hy, b * (x.length / d), 1, b * (z.length / d), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hmul
    · omega
    · exact hmulz
    · calc x = nCopies w (x.length / d) := hxpow
        _ = nCopies (nCopies y b) (x.length / d) := by rw [hweq]
        _ = nCopies y (b * (x.length / d)) := nCopies_compose y b (x.length / d)
    · rw [nCopies_succ, nCopies_zero, List.append_nil]
    · calc z = nCopies w (z.length / d) := hzpow
        _ = nCopies (nCopies y b) (z.length / d) := by rw [hweq]
        _ = nCopies y (b * (z.length / d)) := nCopies_compose y b (z.length / d)
  · have hm2 : 2 ≤ b * y.length / d := by omega
    obtain ⟨v, hv, p, q, hp, hq, hyv, hwv⟩ :=
      pow_pow_commonRoot hy hwne hb hm2 hys
    have hmul1 : 1 ≤ q * (x.length / d) := by
      calc 1 ≤ x.length / d := hwp
        _ ≤ q * (x.length / d) := Nat.le_mul_of_pos_left _ hq
    have hmul2 : 1 ≤ q * (z.length / d) := by
      calc 1 ≤ z.length / d := hzp
        _ ≤ q * (z.length / d) := Nat.le_mul_of_pos_left _ hq
    refine ⟨v, hv, q * (x.length / d), p, q * (z.length / d), ?_, hp, ?_, ?_, ?_, ?_⟩
    · exact hmul1
    · exact hmul2
    · calc x = nCopies w (x.length / d) := hxpow
        _ = nCopies (nCopies v q) (x.length / d) := by rw [hwv]
        _ = nCopies v (q * (x.length / d)) := nCopies_compose v q (x.length / d)
    · exact hyv
    · calc z = nCopies w (z.length / d) := hzpow
        _ = nCopies (nCopies v q) (z.length / d) := by rw [hwv]
        _ = nCopies v (q * (z.length / d)) := nCopies_compose v q (z.length / d)

/-! ## The separator consequence: two excursions cannot have different first letters -/

/-- **The separator step.** If `A^m ++ B^m = U^k` with `m, k >= 2`, `A, B` nonempty and
`(m-1)*|A| >= |U|`, then `A` and `B` start with the same letter. (The hypothesis is
asymmetric because the periodicity lemma is applied to the first excursion `A`; by
symmetry the same conclusion holds with `A` and `B` exchanged and `(m-1)*|B| >= |U|`.)

This is the step the branching construction of `docs/scalar-primitive-spellings-83.md`
needs: cutting a cyclic Eulerian spelling at two visits to a vertex that has two
distinct outgoing edge types produces two closed excursions `A` and `B` whose first
*edge types* differ, hence whose first letters differ. -/
theorem ampbmp_head_eq_of_pow {A B U : List α} {m k : ℕ}
    (hA : A ≠ []) (hB : B ≠ []) (hm2 : 2 ≤ m) (hk2 : 2 ≤ k)
    (h : nCopies A m ++ nCopies B m = nCopies U k)
    (hlen : (m - 1) * A.length ≥ U.length) :
    A[0]? = B[0]? := by
  obtain ⟨w, hw, p, q, r, hp, hq, hr, hA', hB', hU'⟩ :=
    ampbmp_commonRoot hA hB hm2 hm2 (by omega) h hlen
  exact head_eq_of_commonRoot hw hp hq hA' hB'

/-- Consequently, under the same hypotheses, `A^m ++ B^m` is not a proper power: the two
excursions must have started with the same edge type, contradicting the assumption that
the vertex had two distinct outgoing edge types.

**Audit note (2026-09).** The witness `U`, the exponent `k ≥ 2` and the equation
`A^m ++ B^m = U^k` appear here as *hypotheses*, so this is not the primitivity statement
the graph argument needs: it derives the conclusion from an already-contradictory
premise. The quantified form (no witness in sight) is
`LyndonSchutzenberger.not_properPower_of_head_ne`, and the `IsPrimitive` form is
`LyndonSchutzenberger.ampbmp_isPrimitive_of_head_ne`, both proved from the full
Lyndon–Schützenberger theorem. This conditional variant is kept for the record. -/
theorem ampbmp_not_properPower_of_head_ne {A B U : List α} {m k : ℕ}
    (hA : A ≠ []) (hB : B ≠ []) (hm2 : 2 ≤ m) (hk2 : 2 ≤ k)
    (h : nCopies A m ++ nCopies B m = nCopies U k)
    (hlen : (m - 1) * A.length ≥ U.length)
    (hne : A[0]? ≠ B[0]?) :
    ¬ IsProperPower (nCopies A m ++ nCopies B m) := by
  intro hp
  obtain ⟨U, hU, k', hk', heq⟩ := hp
  exact hne (ampbmp_head_eq_of_pow hA hB hm2 hk2 h hlen)

/-- The same statement phrased with `IsPrimitive`.

**Audit note (2026-09).** Inverted form, as above: superseded by
`LyndonSchutzenberger.ampbmp_isPrimitive_of_head_ne`. -/
theorem ampbmp_primitive_of_head_ne {A B U : List α} {m k : ℕ}
    (hA : A ≠ []) (hB : B ≠ []) (hm2 : 2 ≤ m) (hk2 : 2 ≤ k)
    (h : nCopies A m ++ nCopies B m = nCopies U k)
    (hlen : (m - 1) * A.length ≥ U.length)
    (hne : A[0]? ≠ B[0]?) :
    IsPrimitive (nCopies A m ++ nCopies B m) :=
  ampbmp_not_properPower_of_head_ne hA hB hm2 hk2 h hlen hne

/-! ## The graph-side divisibility step -/

/-- The number of occurrences of a letter in a word. -/
def letterCount {α : Type _} [BEq α] (a : α) (l : List α) : ℕ := l.count a

theorem letterCount_append {α : Type _} [BEq α] (a : α) (x y : List α) :
    letterCount a (x ++ y) = letterCount a x + letterCount a y := by
  simp [letterCount, List.count_append]

theorem letterCount_nCopies {α : Type _} [BEq α] (a : α) (l : List α) (k : ℕ) :
    letterCount a (nCopies l k) = k * letterCount a l := by
  induction k with
  | zero => simp [letterCount, nCopies_zero, List.count_nil]
  | succ k ih =>
    rw [nCopies_succ, letterCount_append, ih, Nat.succ_mul]
    omega

/-- In a witness `A^m ++ B^m = U^k`, the exponent `k` divides `m` times the number of
occurrences of each letter in `A ++ B`. This is the counting step that the graph
argument uses: it is what forces `k` to be a divisor of `m` once the relevant letter
counts are coprime (see `dvd_mul_of_letterCount_eq_one`). -/
theorem dvd_mul_letterCount_of_pow {α : Type _} [BEq α] {A B U : List α} {m k : ℕ} (a : α)
    (h : nCopies A m ++ nCopies B m = nCopies U k) :
    k ∣ m * letterCount a (A ++ B) := by
  have h1 : letterCount a (nCopies A m ++ nCopies B m) = letterCount a (nCopies U k) := by
    rw [h]
  have h2 : m * (letterCount a A + letterCount a B) = k * letterCount a U := by
    have h5 := h1
    rw [letterCount_append] at h5
    rw [letterCount_nCopies, letterCount_nCopies, letterCount_nCopies] at h5
    rw [Nat.mul_add]
    exact h5
  have h3 : letterCount a (A ++ B) = letterCount a A + letterCount a B := letterCount_append ..
  have h4 : k ∣ m * (letterCount a A + letterCount a B) := by
    have h5 : k ∣ k * letterCount a U := by
      rw [Nat.mul_comm k (letterCount a U)]
      exact Nat.dvd_mul_left k (letterCount a U)
    rw [← h2] at h5
    exact h5
  rw [← h3] at h4
  exact h4

/-- If some letter occurs exactly once in `A ++ B`, every witness `A^m ++ B^m = U^k`
satisfies `k | m`. Together with `k >= 2` this restricts the possible witnesses to
proper divisors of `m`.

**Audit note (2026-09).** This shape is *not* the inverted one: the conclusion is a
statement about the witness `k` that the caller already possesses, so taking the
equation as a hypothesis is exactly right here. -/
theorem dvd_mul_of_letterCount_eq_one {α : Type _} [BEq α] {A B U : List α} {m k : ℕ} (a : α)
    (hc : letterCount a (A ++ B) = 1) (h : nCopies A m ++ nCopies B m = nCopies U k) :
    k ∣ m := by
  have h1 : k ∣ m * letterCount a (A ++ B) := dvd_mul_letterCount_of_pow a h
  rwa [hc, Nat.mul_one] at h1

/-- A worked example: for the two excursions `[0,1]` and `[1,0]`, whose first letters
differ, the word `A^2 ++ B^2` admits no fourth-power root. The length hypothesis of
`ampbmp_head_eq_of_pow` holds here because `|U| = 2*4/4 = 2 = |A|`. -/
theorem ampbmp_no_pow_four_example :
    ¬ (∃ U : List Nat, (nCopies [0, 1] 2 ++ nCopies [1, 0] 2) = nCopies U 4) := by
  rintro ⟨U, h⟩
  have hne : ([0, 1] : List Nat)[0]? ≠ ([1, 0] : List Nat)[0]? := by simp
  have h2 := congrArg List.length h
  simp only [nCopies_length, List.length_append] at h2
  have hA2 : ([0, 1] : List Nat).length = 2 := rfl
  have hB2 : ([1, 0] : List Nat).length = 2 := rfl
  rw [hA2, hB2] at h2
  have h3 : 4 * 2 = 4 * U.length := by
    have h5 : 2 * 2 + 2 * 2 = 4 * 2 := by omega
    rwa [h5] at h2
  have h4 : U.length = 2 := Nat.eq_of_mul_eq_mul_left (n := 4) (by omega) h3.symm
  have hlen : (2 - 1) * ([0, 1] : List Nat).length ≥ U.length := by
    rw [h4]
    simp
  exact hne
    (ampbmp_head_eq_of_pow (A := [0, 1]) (B := [1, 0]) (U := U) (m := 2) (k := 4) (by simp)
      (by simp) (by omega) (by omega) h hlen)

end AssemblyP1
