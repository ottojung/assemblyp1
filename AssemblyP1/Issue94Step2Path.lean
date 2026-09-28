import AssemblyP1.Issue94OrbitSearch

/-!
# Board 94, front B: `Step2_components_are_paths` is settled outright

`AssemblyP1.Issue89GapMap.Step2_components_are_paths` (`:358`) was recorded as
an open `Prop` with no inhabitant.  This module proves it, **in general**, for
every `K`, every genome and every read length `L`; no bounded search is used
anywhere in the argument.

The statement is: for a chord `{a, b}` of a primitive circle of size `K`, the
truncated backward orbit `{{a - j, b - j} : j ≤ pairBack a b}` visits no
unordered pair twice.  Formally, for `j ≤ pairBack hK S a.val b.val` with
`j ≠ 0` it must **not** be the case that

* `(a - j) ≡ a` and `(b - j) ≡ b (mod K)`, or
* `(a - j) ≡ b` and `(b - j) ≡ a (mod K)`.

The first disjunct is arithmetic: it forces `j ≡ 0 (mod K)`, and `j < K`
comes from `P2RepeatResidual.pairBack_lt_G`, which needs primitivity.
The second disjunct forces `2 * j ≡ 0 (mod K)`, hence `K = 2 * j`, hence
`a ≡ b + j (mod K)`; the backward agreement at `t = j = K/2` then forces
`cyc (a + u) = cyc (a + j + u)` for every `u < K`, i.e. the circular word is
literally `T ++ T` with `|T| = K/2 < K` as seen from any start, which is
shift-invariance by `K/2` and so contradicts `IsPrimitive`.

**Primitivity is therefore genuinely needed, and in both branches.**  That is
exactly what the `decide` results `Issue94OrbitSearch.t_np_3`, `t_np_4` say
(`OrbitExclNP` — the same statement with primitivity dropped — is false at
`K = 3` and `K = 4`).  The previous front's suspicion that `IsPrimitive` is an
artefact of the statement being about the circle rather than the word is
therefore **refuted**: the statement is indeed a theorem about the circle, and
primality is the only hypothesis it needs.

The hypotheses `P2` and `2 ≤ L ≤ K` do **not** occur in the conclusion and are
genuinely unnecessary: the statement is about the circular word alone.  They
are kept as hypotheses so that the library `Prop` is proved verbatim.

The new intermediate results below --- `sub_ne_self`, `swap_forces_half`,
`mod_wrap`, `shiftInvB_of_half` --- are stated locally; `swap_forces_half`
and `shiftInvB_of_half` in particular are general circle lemmas that arguably
belong next to `RepeatAdapter.ShiftInvariant`, and this module does not touch
any library file.
-/

namespace AssemblyP1.Issue94Step2Path

open AssemblyP1
open AssemblyP1.PopulationReduction
open AssemblyP1.P2RepeatResidual
open AssemblyP1.RepeatAdapter
open AssemblyP1.OrientedRigidity
open AssemblyP1.Issue89GapMap
open AssemblyP1.Issue94OrbitSearch

/-! ## 1. Arithmetic on the circle

Everything in this section is elementary and holds for an arbitrary `K`; no
genome structure is used. -/

/-- For `x < K` and `0 < j < K`, the backward residue `(x + K - j) % K` is
never `x` itself.  This is the whole content of the **first disjunct**. -/
theorem sub_ne_self (K : ℕ) (_hK : 0 < K) {x j : ℕ} (hx : x < K) (hj0 : 0 < j)
    (hjK : j < K) (h : (x + K - j) % K = x) : False := by
  by_cases hc : x + K - j < K
  · rw [Nat.mod_eq_of_lt hc] at h
    omega
  · -- `K ≤ x + K - j < 2 * K`, so the residue is `x - j`, which is `< x`.
    have hsub : x + K - j - K < K := by omega
    have hrw : (x + K - j - K) % K = x := by
      calc (x + K - j - K) % K
          = (((x + K - j - K) % K) + (K % K)) % K := by
              rw [Nat.mod_self, Nat.add_zero, Nat.mod_mod]
        _ = ((x + K - j - K) + K) % K := (Nat.add_mod (x + K - j - K) K K).symm
        _ = (x + K - j) % K := by
            rw [show x + K - j - K + K = x + K - j from by omega]
        _ = x := h
    have h1 : x + K - j - K = x := (Nat.mod_eq_of_lt hsub).symm.trans hrw
    omega

/-- The two swapped congruences `(x - j) ≡ y` and `(y - j) ≡ x (mod K)` with
`x, y < K` and `0 < j < K` force `K = 2 * j`, and force `(y + j) % K = x`.

The key step is `Nat.mod_add_mod`: shifting both sides of
`(x + K - j) ≡ y (mod K)` forward by `j` turns `x + K - j` into `x + K`,
which is congruent to `x` again. -/
theorem swap_forces_half (K : ℕ) (hK : 0 < K) {x y j : ℕ} (hx : x < K) (hy : y < K)
    (hj0 : 0 < j) (hjK : j < K)
    (h1 : (x + K - j) % K = y) (h2 : (y + K - j) % K = x) :
    K = 2 * j ∧ (y + j) % K = x := by
  -- From `h1`: `(x + K - j) ≡ y`, shifted forward by `j`, gives `x ≡ y + j`.
  have hyx : (y + j) % K = x := by
    have hmod := Nat.mod_add_mod (x + K - j) K j
    have hc : x + K - j + j = x + K := by omega
    have hrw : ((x + K - j) % K + j) % K = x := by
      rw [hmod, hc, Nat.add_mod, Nat.mod_eq_of_lt hx, Nat.mod_self, Nat.add_zero,
        Nat.mod_eq_of_lt hx]
    rw [h1] at hrw
    omega
  -- From `h2`, symmetrically: `y ≡ x + j`.
  have hxy : (x + j) % K = y := by
    have hmod := Nat.mod_add_mod (y + K - j) K j
    have hc : y + K - j + j = y + K := by omega
    have hrw : ((y + K - j) % K + j) % K = y := by
      rw [hmod, hc, Nat.add_mod, Nat.mod_eq_of_lt hy, Nat.mod_self, Nat.add_zero,
        Nat.mod_eq_of_lt hy]
    rw [h2] at hrw
    omega
  -- Hence `x ≡ x + 2 * j (mod K)`, and `0 < 2 * j < 2 * K` gives `K = 2 * j`.
  have hm : ((x + j) % K + j) % K = (x + 2 * j) % K := by
    rw [Nat.mod_add_mod, show x + j + j = x + 2 * j by omega]
  have h2j : (x + 2 * j) % K = x := calc
    (x + 2 * j) % K = ((x + j) % K + j) % K := hm.symm
    _ = (y + j) % K := by rw [hxy]
    _ = x := hyx
  have hmod2 : x % K = (x + 2 * j) % K := by
    rw [Nat.mod_eq_of_lt hx]
    exact h2j.symm
  have hK2 : K = 2 * j := by
    have hmd := Nat.mod_add_div' (x + 2 * j) K
    have hmul : (x + 2 * j) / K * K = 2 * j := by rw [h2j] at hmd; omega
    have hq1 : (x + 2 * j) / K < 3 := (Nat.div_lt_iff_lt_mul hK).2 (by omega)
    have hq : 0 < (x + 2 * j) / K := by
      by_contra hc
      have hz : (x + 2 * j) / K = 0 := Nat.eq_zero_of_not_pos hc
      rw [hz, zero_mul] at hmul
      omega
    obtain ⟨r, hr⟩ : ∃ r, (x + 2 * j) / K = 1 + r :=
      ⟨(x + 2 * j) / K - 1, by omega⟩
    rw [hr] at hmul
    by_cases hr0 : r = 0
    · rw [hr0] at hmul
      omega
    · have hr1 : r = 1 := by
        have hle : r ≤ 1 := Nat.le_of_lt_succ (show r < 2 from by omega)
        omega
      rw [hr1] at hmul
      omega
  exact ⟨hK2, hyx⟩

/-- Walking the circle from `a` hits every residue: the offset
`(i + K - a) % K` returns to `i`. -/
theorem mod_wrap (K : ℕ) (hK : 0 < K) (a i : ℕ) (ha : a < K) (hi : i < K) :
    ((a + (i + K - a) % K) % K) = i := by
  have hq1 : (i + K - a) / K < 2 := by
    rw [Nat.div_lt_iff_lt_mul hK]
    omega
  have hmain : a + (i + K - a) % K
      = i + K - (i + K - a) / K * K := by
    have hmd := Nat.mod_add_div' (i + K - a) K
    omega
  rw [hmain]
  by_cases hrc : (i + K - a) / K = 0
  · rw [hrc, zero_mul, Nat.sub_zero]
    have hsub : i + K - K < K := by omega
    have hmod : ((i + K - K) % K + K % K) % K = ((i + K - K) + K) % K :=
      (Nat.add_mod (i + K - K) K K).symm
    rw [Nat.mod_self, Nat.add_zero, Nat.mod_mod] at hmod
    have hrw : (i + K - K) % K = (i + K) % K := by
      rw [hmod, show i + K - K + K = i + K from by omega]
    rw [← hrw]
    exact (Nat.mod_eq_of_lt hsub).trans (by omega)
  · have hpos : 0 < (i + K - a) / K := Nat.pos_of_ne_zero hrc
    have hr1' : (i + K - a) / K = 1 := by omega
    rw [hr1', Nat.one_mul, Nat.add_sub_cancel]
    exact Nat.mod_eq_of_lt hi

/-- **Half-period ⇒ non-primitivity.**  If the circular word repeats with
half-period `j = K/2` as seen from one start `a`, then it is shift-invariant
by `j`, in the bounded sense `shiftInvB` of `Issue94OrbitSearch`. -/
theorem shiftInvB_of_half (K : ℕ) (hK : 0 < K) (S : Fin K → Bin) (a j : ℕ)
    (ha : a < K) (hK2 : K = 2 * j)
    (hstep : ∀ t : ℕ, t < K → cyc hK S (a + t) = cyc hK S (a + t + j)) :
    shiftInvB hK S j := by
  have hjK : j < K := by omega
  intro i hi
  have hiK : i < K := Finset.mem_range.mp hi
  have hwrap : ((a + (i + K - a) % K) % K) = i % K := by
    rw [mod_wrap K hK a i ha hiK, Nat.mod_eq_of_lt hiK]
  have hwrap' : ((a + (i + K - a) % K + j) % K) = (i + j) % K := by
    rw [← Nat.mod_add_mod, hwrap, Nat.mod_eq_of_lt hiK]
  exact (cyc_congr hK S hwrap).symm.trans
    ((hstep ((i + K - a) % K) (Nat.mod_lt _ hK)).trans (cyc_congr hK S hwrap'))

/-! ## 2. The two disjuncts -/

/-- **First disjunct is impossible** once `j < K` is known. -/
theorem disj1_false (K : ℕ) (hK : 0 < K) {a j : ℕ} (ha : a < K) (hj0 : 0 < j)
    (hjK : j < K) (h : (a + K - j) % K = a) : False := sub_ne_self K hK ha hj0 hjK h

/-- **Second disjunct forces a half-period**, which contradicts primitivity. -/
theorem disj2_contradicts_prim (K : ℕ) (hK : 0 < K) (S : Fin K → Bin)
    (a b : Fin K) {j : ℕ} (hj0 : 0 < j) (hjK : j < K) (hprim : IsPrimitive hK S)
    (hjle : j ≤ pairBack hK S a.val b.val)
    (h1 : (a.val + K - j) % K = b.val) (h2 : (b.val + K - j) % K = a.val) :
    False := by
  obtain ⟨hK2, hyx⟩ := swap_forces_half K hK a.isLt b.isLt hj0 hjK h1 h2
  have hβle : pairBack hK S a.val b.val ≤ K := (pairBack_spec hK S a.val b.val).2
  obtain ⟨hback, _⟩ := pairBack_spec hK S a.val b.val
  -- `a ≡ b + j (mod K)`, so the two windows compared by `backAgree` at `j`
  -- are the same half-circle read from `a` and from `a + j`.
  have hhalf : ∀ u : ℕ, u < j →
      cyc hK S (a.val + u) = cyc hK S (a.val + u + j) := by
    intro u hu
    have hb := hback (pairBack hK S a.val b.val - j + u) (by omega)
    have hA : a.val + K - pairBack hK S a.val b.val + (pairBack hK S a.val b.val - j + u)
        = a.val + u + j := by omega
    have hB : b.val + K - pairBack hK S a.val b.val + (pairBack hK S a.val b.val - j + u)
        = b.val + j + u := by omega
    have hB' : (b.val + j + u) % K = (a.val + u) % K := by
      calc (b.val + j + u) % K = ((b.val + j) % K + u) % K :=
          (Nat.mod_add_mod (b.val + j) K u).symm
        _ = (a.val + u) % K := by rw [hyx]
    have hc1 : cyc hK S (b.val + K - pairBack hK S a.val b.val
        + (pairBack hK S a.val b.val - j + u)) = cyc hK S (a.val + u) := by
      rw [hB]
      exact cyc_congr hK S hB'
    rw [hA] at hb
    exact (hb.trans hc1).symm
  have hstep : ∀ t : ℕ, t < K →
      cyc hK S (a.val + t) = cyc hK S (a.val + t + j) := by
    intro t ht
    by_cases hc : t < j
    · exact hhalf t hc
    · -- `t = u + j` with `u < j`, so one more turn of the circle is a no-op.
      have hh := hhalf (t - j) (by omega)
      have hq2 : (a.val + (t - j)) % K = (a.val + (t - j) + 2 * j) % K := by
        have hk : a.val + (t - j) + 2 * j = (a.val + (t - j)) + K := by omega
        rw [hk, Nat.add_mod (a.val + (t - j)) K K, Nat.mod_self, Nat.add_zero,
          Nat.mod_mod]
      rw [show a.val + t = a.val + (t - j) + j from by omega]
      calc cyc hK S (a.val + (t - j) + j) = cyc hK S (a.val + (t - j)) := hh.symm
        _ = cyc hK S (a.val + (t - j) + 2 * j) := cyc_congr hK S hq2
        _ = cyc hK S (a.val + (t - j) + j + j) := by
            rw [show a.val + (t - j) + 2 * j = a.val + (t - j) + j + j from by omega]
  have hsi := shiftInvB_of_half K hK S a.val j a.isLt hK2 hstep
  exact hprim j hj0 (by omega) (shiftInv_of_shiftInvB hK S j hsi)

/-! ## 3. The main theorem -/

/-- **`Step2_components_are_paths`, discharged outright, for every `L`.** -/
theorem step2_components_are_paths_proved (L : ℕ) : Step2_components_are_paths L := by
  intro K hK S _hP2 hprim a b hab _hL2 _hLK j hj
  have hKlt : pairBack hK S a.val b.val < K :=
    pairBack_lt_G hK S hprim hab
  have hjK : j < K := by omega
  intro hneg
  obtain ⟨hj0', hdisj⟩ := hneg
  have hj0 : 0 < j := Nat.pos_of_ne_zero hj0'
  rcases hdisj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact disj1_false K hK a.isLt hj0 hjK h1
  · exact disj2_contradicts_prim K hK S a b hj0 hjK hprim hj h1 h2

end AssemblyP1.Issue94Step2Path
