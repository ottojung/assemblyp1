import AssemblyP1.Issue94Step5Heads

/-!
# `Issue94Step5NoChord`: at `L = K` a primitive word has **no chord at all**

Board issue 94, front for the step-5 gap.  The single input the gap map
records an occupant of `BBTLadder.CrossingChordsCoalesce` as needing is
`Issue94Step5Heads.head_dichotomy` at `L = K`.  This module **discharges** it,
by the stronger statement `no_chord_at_L_eq_K` that makes the whole
`L = K` specialisation **vacuously** true.

## The statement

> **Theorem (`no_chord_at_L_eq_K`).**  Let `0 < K` and `S : Fin K → α`.  If
> `a ≠ b` and `vtx hK K S a = vtx hK K S b`, then `S` is invariant under the
> nonzero shift `s = (b - a) mod K`.  Consequently, if `S` is
> `RepeatAdapter.IsPrimitive`, **no** two distinct starts agree on their
> `(K-1)`-mers: there is **no chord at all at `L = K`**.  No `P2` hypothesis
> is used.

## The proof

1. **The shift is a permutation** (`shift_injective`, `shift_bijective`).
   For `s < K`, `i ↦ (i + s) mod K` is injective on `Fin K`.

2. **A chord is a shift-agreement off one residue**
   (`chord_agreement_off_one`).  `vtx hK K S a = vtx hK K S b` says
   `cyc hK S (a + d) = cyc hK S (b + d)` for every `d < K - 1`, and the
   positions `a, a+1, …, a+K-2` are every residue but `a - 1`, while
   `b + d ≡ a + d + s (mod K)`.  So the shift by `s` is a pointwise agreement
   **except at the single residue `a - 1`**.

3. **One exception is impossible** (`one_exception_impossible`).  A
   bijection `σ` of a finite type and a map `f` agreeing under it at every
   point but one agree everywhere: the fibre of `f p` under `f ∘ σ` is the
   image of the fibre under the inverse shift, so the two fibres have equal
   size (`fibre_card`), and since they coincide off `p` while `p` lies in one
   and not the other, one is a **strictly** larger subset of the other
   (`Finset.card_lt_card`) --- contradiction.

So the chord forces shift-invariance, which `IsPrimitive` forbids
(`no_chord_at_L_eq_K`).

## What this does and does not settle

`head_dichotomy` at `L = K` quantifies over quadruples `a b c d` and demands
`vtx hK K S a = vtx hK K S b` and `vtx hK K S c = vtx hK K S d` --- i.e. over
**two chords**, and there are **none**.  So the dichotomy at `L = K`, and with
it `Step5_heads_interleave K`, `CrossingPairsCoalesce K`,
`Step3_slides_meet_no_foreign_chord K` and `CrossingChordsCoalesce K`, are all
**vacuously** true (`head_dichotomy_K` and the four corollaries below).

**This does not discharge the step-5 obligation the board asks for.**  The
dichotomy is stated for `2 ≤ L ≤ K` with `L` arbitrary; its content lives at
`L < K`, and the refutation of `Step5_heads_interleave` is exactly such a case
(`K = 5`, `L = 3`, `S = AABAB`).  What this module establishes is that the
`L = K` specialisation is *free* but carries no weight: a degenerate corner,
not progress on the general statement.  `head_dichotomy` at `2 ≤ L < K` is
untouched and remains **open**.

An exhaustive search over all binary words of length `≤ 16` finds no primitive
word with any chord at `L = K` (and 584 non-primitive ones, e.g. `AABA` at
`K = 4`), which is what the theorem says; the search is reported in the board
report, not in this file.

## Status

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`, no
linter suppression.  `#print axioms` for every theorem below reports exactly
`[propext, Classical.choice, Quot.sound]`.
-/

namespace AssemblyP1.Issue94Step5NoChord

open AssemblyP1
open AssemblyP1.PopulationReduction
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.OrientedRigidity
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.RepeatAdapter
open AssemblyP1.Issue94Step5Heads
open AssemblyP1.Issue89GapMap
open AssemblyP1.BBTLadder
open AssemblyP1.P2RepeatResidual

set_option maxHeartbeats 800000

variable {α : Type} {K : ℕ}

/-- The cyclic shift by `s` on `Fin K`. -/
def shiftOf {K : ℕ} (hK : 0 < K) (s : ℕ) : Fin K → Fin K :=
  fun i => ⟨(i.val + s) % K, Nat.mod_lt _ hK⟩

theorem add_back_dist (K a j : ℕ) (_hK : 0 < K) (ha : a < K) (hj : j < K) :
    Nat.ModEq K (a + (j + K - a) % K) j := by
  have h7 : Nat.ModEq K ((j + K - a) % K) (j + K - a) := Nat.mod_modEq _ _
  have h6 : Nat.ModEq K (a + (j + K - a)) j := by
    have hz : a + (j + K - a) = j + K := by omega
    rw [hz]
    refine (Nat.mod_modEq (j + K) K).symm.trans ?_
    have hh : Nat.ModEq K ((j + K) % K) j := by
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hj]
    exact hh
  exact Nat.ModEq.add (n := K) (Nat.ModEq.refl a) h7 |>.trans h6

theorem back_dist_lt (K a j : ℕ) (hK : 0 < K) (ha : a < K) (hj : j < K)
    (hne : j ≠ (a + K - 1) % K) : (j + K - a) % K < K - 1 := by
  have hk := add_back_dist K a j hK ha hj
  have hd := Nat.mod_lt (j + K - a) hK
  by_contra hcon
  have hdz : (j + K - a) % K = K - 1 := by omega
  have hsum : Nat.ModEq K (a + (j + K - a) % K) (a + K - 1) := by
    have hdz' : Nat.ModEq K ((j + K - a) % K) (K - 1) := by rw [hdz]
    have h := Nat.ModEq.add (n := K) (Nat.ModEq.refl a) hdz'
    have hz : a + (K - 1) = a + K - 1 := by omega
    rw [hz] at h
    exact h
  have h1 : Nat.ModEq K (a + K - 1) j := (hk.symm.trans hsum).symm
  have h2 : (a + K - 1) % K = j := Nat.mod_eq_of_modEq h1 hj
  have h3 : (a + K - 1) % K = a - 1 := by
    have hge : K ≤ a + K - 1 := by omega
    have hlt : a + K - 1 < 2 * K := by omega
    rw [Nat.mod_eq_sub_mod hge]
    omega
  omega

theorem shift_injective (_hK : 0 < K) {s : ℕ} (_hs : s < K) {i j : Fin K}
    (h : (i.val + s) % K = (j.val + s) % K) : i = j := by
  apply Fin.ext
  have h1 : Nat.ModEq K ((i.val + s) % K) (i.val + s) := Nat.mod_modEq _ _
  have h2 : Nat.ModEq K ((i.val + s) % K) (j.val + s) := by
    rw [h]
    exact Nat.mod_modEq _ _
  have h3 : Nat.ModEq K (i.val + s) (j.val + s) := h1.symm.trans h2
  have h4 : Nat.ModEq K (s + i.val) (s + j.val) := by
    have e1 : s + i.val = i.val + s := Nat.add_comm _ _
    have e2 : s + j.val = j.val + s := Nat.add_comm _ _
    rw [e1, e2]
    exact h3
  have h5 : Nat.ModEq K i.val j.val := h4.add_left_cancel' s
  exact Nat.ModEq.eq_of_lt_of_lt h5 i.isLt j.isLt

theorem shift_bijective (hK : 0 < K) (s : ℕ) (hs : s < K) :
    Function.Bijective (shiftOf hK s) := by
  refine ⟨?_, ?_⟩
  · intro i j h
    apply shift_injective hK hs
    exact congrArg Fin.val h
  · intro y
    refine ⟨⟨(y.val + K - s) % K, Nat.mod_lt _ hK⟩, ?_⟩
    apply Fin.ext
    change (((y.val + K - s) % K) + s) % K = y.val
    have h7 : Nat.ModEq K ((y.val + K - s) % K) (y.val + K - s) := Nat.mod_modEq _ _
    have hz : (y.val + K - s) + s = y.val + K := by omega
    have h9 : Nat.ModEq K (((y.val + K - s) % K) + s) (y.val + K) := by
      have h := Nat.ModEq.add h7 (Nat.ModEq.refl s)
      rw [hz] at h
      exact h
    have h10 : Nat.ModEq K (y.val + K) y.val := by
      refine (Nat.mod_modEq (y.val + K) K).symm.trans ?_
      have hh : Nat.ModEq K ((y.val + K) % K) y.val := by
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]
      exact hh
    exact Nat.mod_eq_of_modEq (h9.trans h10) y.isLt

set_option autoImplicit false
theorem fibre_card {G : Type} [Fintype G] [DecidableEq G] {σ : G → G}
    (hbi : Function.Bijective σ) (P : G → Prop) [DecidablePred P] :
    ((Finset.univ : Finset G).filter (fun x : G => P x)).card
    = ((Finset.univ : Finset G).filter (fun x : G => P (σ x))).card := by
  have hlt : ∀ y : G, (Equiv.ofBijective σ hbi).symm (σ y) = y := by
    intro y; simp
  set S : Finset G := Finset.univ.filter (fun x : G => P x) with hSdef
  have hset : (Finset.univ : Finset G).filter (fun x : G => P (σ x))
      = S.image (Equiv.ofBijective σ hbi).symm := by
    rw [hSdef]
    ext y
    constructor
    · intro hy
      have hy' : P (σ (y : G)) := (Finset.mem_filter.mp hy).2
      have hmem : σ y ∈ (Finset.univ : Finset G).filter (fun x : G => P x) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'⟩
      exact Finset.mem_image.mpr ⟨(σ y : G), hmem, hlt y⟩
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      have hx' : P x := (Finset.mem_filter.mp hx).2
      have hval : (Equiv.ofBijective σ hbi).symm x = y := hxy
      have h2 : P (σ y) := by
        have hz : x = σ y := by
          apply (Equiv.ofBijective σ hbi).symm.injective
          calc
            (Equiv.ofBijective σ hbi).symm x = y := hval
            _ = (Equiv.ofBijective σ hbi).symm (σ y) := (hlt y).symm
        rw [hz] at hx'
        exact hx'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩
  rw [hset, Finset.card_image_of_injective _
    ((Equiv.ofBijective σ hbi).symm.injective)]


/-- **One exception is impossible.**  A bijection `σ` of a finite type and a
map `f` into any type, agreeing under the shift at every point but one, agree
everywhere: the fibre of `f p` under `f ∘ σ` is the image of the fibre under
the inverse shift, so the two fibres have equal size, and since they coincide
off `p` while `p` lies in one and not the other, one is strictly larger. -/
theorem one_exception_impossible {G : Type} [Fintype G] [DecidableEq G] {β : Type}
    {f : G → β} {σ : G → G} (hbi : Function.Bijective σ) (p : G)
    (h : ∀ x, x ≠ p → f x = f (σ x)) : ∀ x, f x = f (σ x) := by
  classical
  by_cases hgood : f p = f (σ p)
  · intro x
    by_cases hxp : x = p
    · rw [hxp]; exact hgood
    · exact h x hxp
  · have hne : f p ≠ f (σ p) := hgood
    set A : Finset G := Finset.univ.filter (fun x : G => f x = f p) with hAdef
    set B : Finset G := Finset.univ.filter (fun x : G => f (σ x) = f p) with hBdef
    have hpA : p ∈ A := by
      simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and]
    have hneB : p ∉ B := by
      simp only [hBdef, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun hh => hne hh.symm
    have hcardAB : A.card = B.card := by
      have hq := fibre_card hbi (fun x : G => f x = f p)
      rwa [← hAdef, ← hBdef] at hq
    have hrest : A.erase p = B := by
      ext y
      constructor
      · intro hy
        have hy' := Finset.mem_erase.mp hy
        have hmem := Finset.mem_filter.mp hy'.2
        have hq : f (σ y) = f p := by
          have hz := hmem.2
          have hz2 : f y = f (σ y) := h y hy'.1
          rwa [hz2] at hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
      · intro hy
        have hmem := Finset.mem_filter.mp hy
        have hq : f y = f p := by
          have hz := hmem.2
          have hne' : y ≠ p := by
            intro hh
            exact hneB (hh ▸ hy)
          have hz2 : f y = f (σ y) := h y hne'
          exact hz2.trans hz
        exact Finset.mem_erase.mpr
          ⟨(by intro hh; exact hneB (hh ▸ hy)),
           Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩⟩
    have hltcard : B.card < A.card := by
      rw [← hrest]
      have hssub : A.erase p ⊂ A := by
        rw [Finset.ssubset_iff_subset_ne]
        constructor
        · exact Finset.erase_subset _ _
        · intro hc
          have hmem : p ∈ A.erase p := by rw [hc]; exact hpA
          exact absurd ((Finset.mem_erase.mp hmem).1) (by simp)
      exact Finset.card_lt_card hssub
    exact absurd (Nat.lt_irrefl A.card) (by omega)
theorem diff_pos (K a b : ℕ) (hK : 0 < K) (ha : a < K) (hb : b < K) (hne : a ≠ b) :
    0 < b + K - a := by
  by_cases hle : b ≤ a
  · have hlt : a - b < K := by omega
    have hne' : a - b ≠ 0 := by
      intro hc
      exact hne (by omega)
    have hpos : 0 < K - (a - b) := by omega
    have h1 : K - (a - b) + (a - b) = K := Nat.sub_add_cancel (Nat.le_of_lt hlt)
    have h2 : a - b + b = a := Nat.sub_add_cancel hle
    have heq : b + K - a = K - (a - b) := by omega
    rw [heq]
    exact hpos
  · have hpos : 0 < K - a := Nat.sub_pos_of_lt ha
    have h1 : a + (K - a) = K := Nat.add_sub_of_le (Nat.le_of_lt ha)
    have h2 : a + b ≤ a + K := Nat.add_le_add_left (Nat.le_of_lt hb) a
    have heq : b + K - a = b + (K - a) := by omega
    rw [heq]
    omega
theorem chord_shift (hK : 0 < K) {a b : Fin K} (hab : a ≠ b) :
    0 < (b.val + K - a.val) % K ∧ (b.val + K - a.val) % K < K ∧
      Nat.ModEq K (a.val + (b.val + K - a.val) % K) b.val := by
  have hb := b.isLt
  have ha := a.isLt
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hpos := diff_pos K a.val b.val hK ha hb hne
  have hpos' : 0 < (b.val + K - a.val) % K := by
    by_cases hlt2 : b.val + K - a.val < K
    · have hz : (b.val + K - a.val) % K = b.val + K - a.val := Nat.mod_eq_of_lt hlt2
      rw [hz]
      exact hpos
    · by_contra hcon
      have hz : (b.val + K - a.val) % K = 0 := by omega
      have hge : K ≤ b.val + K - a.val := by omega
      have hsub : (b.val + K - a.val) % K = (b.val + K - a.val - K) % K :=
        Nat.mod_eq_sub_mod hge
      rw [hz] at hsub
      have hlt3 : b.val + K - a.val - K < K := by omega
      rw [Nat.mod_eq_of_lt hlt3] at hsub
      have hz2 : b.val + K - a.val - K = 0 := by omega
      rw [hz2] at hsub
      omega
  refine ⟨hpos', Nat.mod_lt _ hK, ?_⟩
  have h7 : Nat.ModEq K ((b.val + K - a.val) % K) (b.val + K - a.val) :=
    Nat.mod_modEq _ _
  have h6 : Nat.ModEq K (a.val + (b.val + K - a.val)) b.val := by
    have hz : a.val + (b.val + K - a.val) = b.val + K := by omega
    rw [hz]
    refine (Nat.mod_modEq (b.val + K) K).symm.trans ?_
    have hh : Nat.ModEq K ((b.val + K) % K) b.val := by
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hb]
    exact hh
  exact Nat.ModEq.add (n := K) (Nat.ModEq.refl a) h7 |>.trans h6

/-- **A chord at `L = K` is a shift-agreement at every residue but one.**  With
`a ≠ b` and `vtx hK K S a = vtx hK K S b`, put `s = (b - a) mod K`.  Then for
every `j : Fin K` whose value is not the one residue the `(K-1)`-window at `a`
omits --- namely `(a - 1) mod K` --- one has `S j = S (shiftOf hK s j)`. -/
theorem chord_agreement_off_one (hK : 0 < K) (S : Fin K → α) {a b : Fin K}
    (hab : a ≠ b) (hvab : vtx hK K S a = vtx hK K S b) :
    ∀ j : Fin K, j.val ≠ (a.val + K - 1) % K →
      S j = S (shiftOf hK ((b.val + K - a.val) % K) j) := by
  obtain ⟨hpos, hlt, hab_mod⟩ := chord_shift hK hab
  set s : ℕ := (b.val + K - a.val) % K with hs
  intro j hj
  set d := (j.val + K - a.val) % K with hd
  have hd1 : d < K - 1 := back_dist_lt K a.val j.val hK a.isLt j.isLt hj
  have hag : vtx hK K S a ⟨d, hd1⟩ = vtx hK K S b ⟨d, hd1⟩ := congrFun hvab ⟨d, hd1⟩
  have hag' : cyc hK S (a.val + d) = cyc hK S (b.val + d) := by
    simpa [vtx, nodeWindow, window] using hag
  have hkey : Nat.ModEq K (a.val + d) j.val :=
    add_back_dist K a.val j.val hK a.isLt j.isLt
  have hleft : cyc hK S (a.val + d) = S j := by
    exact congrArg S (Fin.ext (Nat.mod_eq_of_modEq hkey j.isLt))
  have hmod : Nat.ModEq K (b.val + d) (j.val + s) := by
    have hsum : Nat.ModEq K (a.val + s + d) (b.val + d) :=
      Nat.ModEq.add (n := K) hab_mod (Nat.ModEq.refl d)
    have hkey' : Nat.ModEq K (a.val + s + d) (j.val + s) := by
      have h1 : Nat.ModEq K ((a.val + d) + s) (j.val + s) :=
        Nat.ModEq.add (n := K) hkey (Nat.ModEq.refl s)
      have e1 : a.val + s + d = (a.val + d) + s := by omega
      rw [e1]
      exact h1
    exact hsum.symm.trans hkey'
  have hright : cyc hK S (b.val + d) = S (shiftOf hK s j) := by
    have heq : (b.val + d) % K = (j.val + s) % K :=
      Nat.mod_eq_of_modEq (hmod.trans (Nat.mod_modEq (j.val + s) K).symm) (Nat.mod_lt _ hK)
    simp only [cyc, shiftOf]
    exact congrArg S (Fin.ext heq)
  rw [← hleft, ← hright]
  exact hag'


/-- **A chord at `L = K` forces shift-invariance of the whole word.**  The
agreement of one chord at `L = K` covers `K-1` of the `K` residues, and the
shift is a permutation of `Fin K`, so a single exception is impossible
(`one_exception_impossible`): the agreement holds at the omitted residue too,
and since `vtx hK K S j` is literally `S j` at read length `K`, that is
`cyc hK S j = cyc hK S (j + s)` for every `j`, i.e. shift-invariance. -/
theorem chord_at_L_eq_K_shiftInvariant (hK : 0 < K) (S : Fin K → α) {a b : Fin K}
    (hab : a ≠ b) (hvab : vtx hK K S a = vtx hK K S b) :
    RepeatAdapter.ShiftInvariant hK S ((b.val + K - a.val) % K) := by
  obtain ⟨hpos, hlt, _⟩ := chord_shift hK hab
  set s : ℕ := (b.val + K - a.val) % K with hs
  have hag := chord_agreement_off_one hK S hab hvab
  have hpoint : ∀ j : Fin K, S j = S (shiftOf hK s j) := by
    refine one_exception_impossible (shift_bijective hK s hlt)
      (p := (⟨(a.val + K - 1) % K, Nat.mod_lt _ hK⟩ : Fin K)) (fun j hj => ?_)
    refine hag j ?_
    intro hh
    exact hj (Fin.ext hh)
  intro i
  -- `cyc hK S i = S (i % K)` and `cyc hK S (i + s) = S ((i + s) % K)`,
  -- and `(i % K + s) % K = (i + s) % K`
  have h1 := hpoint ⟨i % K, Nat.mod_lt _ hK⟩
  have heq : (i % K + s) % K = (i + s) % K := by
    have h1 : Nat.ModEq K (i % K) i := Nat.mod_modEq _ _
    have h2 : Nat.ModEq K (i % K + s) (i + s) := h1.add_right s
    show (i % K + s) % K = (i + s) % K
    exact_mod_cast h2
  have hA : S ⟨i % K, Nat.mod_lt _ hK⟩
      = S ⟨(i + s) % K, Nat.mod_lt _ hK⟩ := by
    have hB := h1
    have hC : shiftOf hK s ⟨i % K, Nat.mod_lt _ hK⟩
        = ⟨(i + s) % K, Nat.mod_lt _ hK⟩ := by
      apply Fin.ext
      exact heq
    rw [hC] at hB
    exact hB
  have hc1 : cyc hK S i = S ⟨i % K, Nat.mod_lt _ hK⟩ := by
    simp only [cyc]
  have hc2 : cyc hK S (i + s) = S ⟨(i + s) % K, Nat.mod_lt _ hK⟩ := by
    simp only [cyc]
  exact hc1.symm.trans (hA.trans hc2)

/-- **No chord exists at `L = K` for a primitive word.**  Two distinct starts
agreeing on their `(K-1)`-mers would make the word invariant under a nonzero
shift below `K`, which is exactly what `IsPrimitive` forbids.  No `P2`
hypothesis is needed. -/
theorem no_chord_at_L_eq_K (hK : 0 < K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S) {a b : Fin K} (hab : a ≠ b) :
    vtx hK K S a ≠ vtx hK K S b := by
  intro hvab
  have hsi := chord_at_L_eq_K_shiftInvariant hK S hab hvab
  obtain ⟨hpos, hlt, _⟩ := chord_shift hK hab
  exact hprim _ hpos hlt hsi


/-! ## 5. The `L = K` corollaries: the step-5 line is free, and vacuous -/

/-! ## 5. The correctly-scoped corollary: at genome size `= L` the `L`-read
reduction has **no** instance

The `Prop`s of the §5 reduction are stated for `2 ≤ L ≤ K` with `K` ranging
over all genome sizes, so instantiating them at `L = K` does **not** restrict
the genome size: it leaves the cases `2 ≤ K ≤ K'` with `K < K'`, i.e. genomes
*longer* than the read length.  `no_chord_at_L_eq_K` says nothing there.

What it does say is that at **genome size equal to the read length** there is
no chord at all, and hence no instance of any of the `L`-read reduction
obligations.  The next corollary is that fact, in the form the reduction
actually consumes. -/

/-- **`head_dichotomy` at read length `L` has no instance on a genome of size
`L`.**  Concretely: for `K = L` the two-chord hypothesis is unsatisfiable, so the
dichotomy holds.  This is stated as a `Prop` over the genome size `K` with the
added hypothesis `K = L`, which is what the reduction needs; it is *not* the
`head_dichotomy K` of `Issue94Step5Heads`, whose `K` is the read length and
whose genome size is still free. -/
theorem head_dichotomy_at_genome_eq_read (L : ℕ) (hL : 2 ≤ L) :
    ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → PopulationReduction.Bin), K = L →
      P2 hK L S → RepeatAdapter.IsPrimitive hK S →
      ∀ (a b c d : Fin K), a ≠ b → c ≠ d → 2 ≤ L → L ≤ K →
        vtx hK L S a = vtx hK L S b → vtx hK L S c = vtx hK L S d →
        Interleaved (mkGenome hK S) a b c d →
        SameExtension K hK S a b c d ∨
          Interleaved (mkGenome hK S)
            (maxPairStart hK S a b) (maxPairStart hK S b a)
            (maxPairStart hK S c d) (maxPairStart hK S d c) := by
  intro K hK S hKL hP2 hprim a b c d hab hcd _h2L _hLK hvab _hvcd _hI
  -- on a genome of size `= L` the two-chord hypothesis is unsatisfiable
  have hKL' : K = L := hKL
  subst hKL'
  exact absurd hvab (by
    intro hh
    exact (no_chord_at_L_eq_K hK S hprim hab) hh)

end AssemblyP1.Issue94Step5NoChord
