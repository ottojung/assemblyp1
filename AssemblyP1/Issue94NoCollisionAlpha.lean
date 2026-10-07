import AssemblyP1.Issue94NoCollision
import AssemblyP1.Issue94HeadCollision

/-!
# `Issue94NoCollisionAlpha`: the refuted case at an arbitrary alphabet

Board issue 94.  `Issue94NoCollision.lean` states its fourteen substantive
theorems over `S : Fin K → PopulationReduction.Bin`, while the target
`BBTCrossingCoalesce.CrossingPairsCoalesce` (`BBTCrossingCoalesce.lean:212`)
is stated under `variable {α : Type} [DecidableEq α]` (`BBTCrossingCoalesce.lean:107`)
and quantifies over `S : Fin K → α`.  The composite `Issue94CaseSplit` therefore
closes only at `α = Bin`, leaving a residual assumption on definition-of-done
item 2.  Fronts 94b4 and 94d4 both recorded this as the outstanding gap.

## What this file establishes

**The `Bin` restriction was inherited plumbing, not mathematics.**  Every
dependency the no-collision argument actually uses is already stated for an
arbitrary `[DecidableEq α]`:

| dependency | where | alphabet |
|---|---|---|
| `P2` | `P2.lean:80` | `{α} [DecidableEq α]` |
| `P2.imp_ExtCrossing` | `P2RepeatResidual.lean:903` | `{α}` |
| `vtx_eq_iff`, `vtx_maxPairStart` | `BBTCrossingCoalesce.lean:114, 194` | `{α}` |
| `collision_forces_pair`, `three_starts_ne` | `BBTCrossingCoalesce.lean:173, 137` | `{α}` |
| `pairBack`, `pairBack_spec`, `pairBack_ge`, `pairBack_lt_G`, `pairBack_comm` | `P2RepeatResidual.lean:419, 426, 436, 654, 712` | `{α}` |
| `pairBack_shift` | `P2RepeatResidual.lean:540` | `{α}` |
| `chord_shift_left` | `P2RepeatResidual.lean:497` | `{α}` |
| `maxPairStart_eq` | `BBTLadder.lean:159` | `{α}` |
| `cyc_congr` | `BBTLadder.lean:419` | `{α}` |
| `rotAdd`, `rotAdd_comp`, `rotAdd_K`, `rotAdd_inj` | `BBTChords.lean`, `Issue94IterSlide.lean:67, 76` | alphabet-free |
| `interleaved_iff`, `step4_slide_iterates_word` | `Issue94IterSlide.lean:407, 440` | `{α}` |
| `SlideGuards` | `Issue94IterSlide.lean:344` | alphabet-free |

The three genuinely `Bin`-typed items on the old path were all *wrappers*:

* `Issue94Step4Prop.step4_guarded` (`:153`), whose **proof body is a call to the
  α-general `step4_slide_iterates_word` at read length `t ≤ K`**, and whose
  `t ≤ K` comes from `pairBack_le_K` = `pairBack_spec hK S a b).2`, itself
  α-general. The wrapper is re-proved here as `step4_guarded_alpha` and is
  *literally the same argument*.
* `Issue89GapMap.step3_shared_endpoint_forces_pair_readL` (`:558`), which is a
  four-case composition of the α-general `collision_forces_pair` and
  `three_starts_ne`. Re-proved here as `step3_shared_endpoint_alpha`, case for
  case, from the same two lemmas.
* `Issue94Step5Heads.heads_of_one_chord_ne` (`:251`), which is a two-line call to
  `maxPair_isRepeat`. **Replaced, not re-derived**, by the already-existing
  α-general `Issue94HeadCollision.heads_ne_of_chord` (`Issue94HeadCollision.lean:80`),
  as 94d4's E11 anticipated. The two have identical statements up to the alphabet
  binder.

The only genuinely new lemma is `pairBack_mod_alpha`. The old `pairBack_mod`
routed through the `Bin`-typed computable restatement `backAgreeC` /
`backSetC` (`Issue94OrbitSearch.lean:68, 76`); that restatement exists only so
`pairBackC` can be *computed* during the orbit search, and it is not needed for
the mathematical content. This file proves the same period-`K` invariance
directly against the α-general `pairBack_ge` / `pairBack_spec`.

## Status of the no-collision arm

Unchanged and not re-litigated: this is the **refuted case** of the split. Its
hypothesis set is empty on every regime an exhaustive binary sweep reaches
(`K ≤ 9`: 7704 admissible interleaving chord quadruples, 0 satisfying all four
cross-head inequalities), so the composite rests on the collision half alone.
That sweep is finite evidence, not a kernel proof, and it is `Bin`-only. Nothing
in this file shows the arm empty for larger alphabets, and nothing in it shows
the arm non-empty either.
-/

namespace AssemblyP1.Issue94NoCollisionAlpha

open AssemblyP1 AssemblyP1.PopulationReduction AssemblyP1.RepeatAdapter
open AssemblyP1.SourceFaithfulIs AssemblyP1.OrientedRigidity AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTChords AssemblyP1.BBTUniqueEulerian AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTLadder AssemblyP1.BBTCrossingCoalesce AssemblyP1.Issue89GapMap
open AssemblyP1.Issue94OrbitSearch AssemblyP1.Issue94OrbitGeneral
open AssemblyP1.Issue94IterSlide AssemblyP1.Issue94Step2Path
open AssemblyP1.Issue94Step4Prop AssemblyP1.Issue94Step5Heads
open AssemblyP1.Issue94NoCollision AssemblyP1.Issue94HeadCollision

set_option maxHeartbeats 800000
variable {K L : ℕ}
variable {α : Type} [DecidableEq α]

/-! ## 1. The one genuinely new lemma: `pairBack` is `K`-periodic -/

/-- The `backAgree` predicate of `P2RepeatResidual`, made public and generalised.
`P2RepeatResidual.backAgree` is `private`, so the α-general maximality step has
to be restated here. This is the same `Prop` by definition. -/
def backAgreeA (hK : 0 < K) (S : Fin K → α) (a b t : ℕ) : Prop :=
  ∀ u : ℕ, u < t → cyc hK S (a + K - t + u) = cyc hK S (b + K - t + u)

theorem backAgreeA_mod (hK : 0 < K) (S : Fin K → α) (x y t : ℕ) (ht : t ≤ K) :
    backAgreeA hK S x y t ↔ backAgreeA hK S (x % K) (y % K) t := by
  have mdl : ∀ (z u : ℕ), (z + K - t + u) % K = ((z % K) + K - t + u) % K := by
    intro z u
    rw [Nat.add_sub_assoc ht, Nat.add_assoc, Nat.add_sub_assoc ht, Nat.add_assoc, modadd]
  constructor
  · intro h u hu
    have hh := h u hu
    calc cyc hK S ((x % K) + K - t + u) = cyc hK S (x + K - t + u) := by
          symm; exact BBTLadder.cyc_congr hK S (x + K - t + u) ((x % K) + K - t + u) (mdl x u)
      _ = cyc hK S (y + K - t + u) := hh
      _ = cyc hK S ((y % K) + K - t + u) := BBTLadder.cyc_congr hK S (y + K - t + u) ((y % K) + K - t + u) (mdl y u)
  · intro h u hu
    have hh := h u hu
    calc cyc hK S (x + K - t + u) = cyc hK S ((x % K) + K - t + u) :=
          BBTLadder.cyc_congr hK S (x + K - t + u) ((x % K) + K - t + u) (mdl x u)
      _ = cyc hK S ((y % K) + K - t + u) := hh
      _ = cyc hK S (y + K - t + u) := by
          symm; exact BBTLadder.cyc_congr hK S (y + K - t + u) ((y % K) + K - t + u) (mdl y u)

/-- **`pairBack` is `K`-periodic, for an arbitrary alphabet.**  The α-general
replacement for `Issue94NoCollision.pairBack_mod`, proved against the
α-general `pairBack_ge` and `pairBack_spec` rather than through the `Bin`-typed
computable restatement `backAgreeC`. -/
theorem pairBack_mod_alpha (hK : 0 < K) (S : Fin K → α) (x y : ℕ) :
    pairBack hK S x y = pairBack hK S (x % K) (y % K) := by
  classical
  obtain ⟨hA, hB⟩ := pairBack_spec hK S x y
  obtain ⟨hA2, hB2⟩ := pairBack_spec hK S (x % K) (y % K)
  have fwd : backAgreeA hK S x y (pairBack hK S x y) →
      backAgreeA hK S (x % K) (y % K) (pairBack hK S x y) :=
    (backAgreeA_mod hK S x y (pairBack hK S x y) hB).mp
  refine le_antisymm
    (pairBack_ge hK S (x % K) (y % K) (pairBack hK S x y) hB (fwd hA))
    (pairBack_ge hK S x y (pairBack hK S (x % K) (y % K)) hB2
      ((backAgreeA_mod hK S x y (pairBack hK S (x % K) (y % K)) hB2).mpr hA2))

/-! ## 2. The slide machinery, at an arbitrary alphabet -/

theorem pairBack_slide_alpha (hK : 0 < K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S)
    {c d : Fin K} (hcd : c ≠ d) (j : ℕ) (hj : j ≤ pairBack hK S c.val d.val) :
    pairBack hK S (rotAdd hK (K - j) c).val (rotAdd hK (K - j) d).val
      = pairBack hK S c.val d.val - j := by
  have hlt : pairBack hK S c.val d.val < K := pairBack_lt_G hK S hprim hcd
  have h := pairBack_shift hK S (a := c) (b := d) j hj hlt
  have hb : pairBack hK S ((c.val + K - j) % K) ((d.val + K - j) % K)
      = pairBack hK S c.val d.val - j :=
    (pairBack_mod_alpha hK S (c.val + K - j) (d.val + K - j)).symm.trans h
  have eA : (rotAdd hK (K - j) c).val = (c.val + K - j) % K := by
    rw [rotAdd_val]; congr 1; omega
  have eB : (rotAdd hK (K - j) d).val = (d.val + K - j) % K := by
    rw [rotAdd_val]; congr 1; omega
  rw [eA, eB]
  exact hb

theorem head_of_slide_alpha (hK : 0 < K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S)
    {a b : Fin K} (hab : a ≠ b) (j : ℕ) (hj : j ≤ pairBack hK S a.val b.val) :
    maxPairStart hK S (rotAdd hK (K - j) a) (rotAdd hK (K - j) b)
      = maxPairStart hK S a b := by
  rw [maxPairStart_eq, maxPairStart_eq]
  have h := pairBack_slide_alpha hK S hprim hab j hj
  rw [h]
  rw [rotAdd_comp hK (K - (pairBack hK S a.val b.val - j)) (K - j)]
  have key : (K - (pairBack hK S a.val b.val - j)) + (K - j)
      = (K - pairBack hK S a.val b.val) + K := by
    have hβ : pairBack hK S a.val b.val ≤ K := (pairBack_spec hK S a.val b.val).2
    have h1 : K - (pairBack hK S a.val b.val - j) = K - pairBack hK S a.val b.val + j := by
      omega
    omega
  rw [key, rotAdd_addK]

theorem pairBack_of_head_alpha (hK : 0 < K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S)
    {a b : Fin K} (hab : a ≠ b) :
    pairBack hK S (maxPairStart hK S a b).val (maxPairStart hK S b a).val = 0 := by
  have hlt : pairBack hK S a.val b.val < K := pairBack_lt_G hK S hprim hab
  have h := pairBack_shift hK S (a := a) (b := b) (pairBack hK S a.val b.val)
    (le_refl _) hlt
  have hz : pairBack hK S (a.val + K - pairBack hK S a.val b.val)
      (b.val + K - pairBack hK S a.val b.val) = 0 := by omega
  have hb := (pairBack_mod_alpha hK S (a.val + K - pairBack hK S a.val b.val)
      (b.val + K - pairBack hK S a.val b.val)).symm.trans hz
  have eA : (maxPairStart hK S a b).val = (a.val + K - pairBack hK S a.val b.val) % K := by
    rw [maxPairStart, Fin.val_mk]
  have eB : (maxPairStart hK S b a).val = (b.val + K - pairBack hK S a.val b.val) % K := by
    rw [maxPairStart, Fin.val_mk, pairBack_comm]
  rw [eA, eB]
  exact hb

theorem head_of_head_alpha (hK : 0 < K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S) {a b : Fin K} (hab : a ≠ b) :
    maxPairStart hK S (maxPairStart hK S a b) (maxPairStart hK S b a) = maxPairStart hK S a b
      ∧ maxPairStart hK S (maxPairStart hK S b a) (maxPairStart hK S a b) = maxPairStart hK S b a := by
  constructor
  · rw [maxPairStart_eq, show K - pairBack hK S (maxPairStart hK S a b).val (maxPairStart hK S b a).val = K from by
      rw [pairBack_of_head_alpha hK S hprim hab, Nat.sub_zero], rotAdd_K]
  · have hph := pairBack_of_head_alpha hK S hprim hab
    rw [maxPairStart_eq]
    have hc := pairBack_comm hK S (maxPairStart hK S b a).val (maxPairStart hK S a b).val
    have hz : pairBack hK S (maxPairStart hK S b a).val (maxPairStart hK S a b).val = 0 := by
      rw [← hc, hph]
    rw [hz, Nat.sub_zero, rotAdd_K]

/-! ## 3. A chord stays a chord, and stays a pair, under a slide -/

theorem chord_of_slide_alpha (hK : 0 < K) (S : Fin K → α)
    {a b : Fin K} (hv : vtx hK L S a = vtx hK L S b) (j : ℕ)
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

omit [DecidableEq α] in
theorem slide_pair_ne_alpha (hK : 0 < K) (_S : Fin K → α)
    {a b : Fin K} (hab : a ≠ b) (j : ℕ) :
    rotAdd hK (K - j) a ≠ rotAdd hK (K - j) b :=
  fun hh => hab (rotAdd_inj_any hK (K - j) hh)

/-! ## 4. The two `Bin` wrappers, re-proved at an arbitrary alphabet -/

/-- **§5 step 3 at an arbitrary alphabet.**  This is
`Issue89GapMap.step3_shared_endpoint_forces_pair_readL` (`:558`) with its `Bin`
binder removed. The old lemma is a four-case composition of the two α-general
lemmas `collision_forces_pair` and `three_starts_ne`; the four cases below are
those four cases, unchanged, with no new mathematical content. -/
theorem step3_shared_endpoint_alpha (hK : 0 < K) (S : Fin K → α)
    (h2L : 2 ≤ L) (hLK : L ≤ K) (hP2 : P2 hK L S) (hprim : RepeatAdapter.IsPrimitive hK S)
    {a b c d : Fin K} (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d)
    (h : a = c ∨ a = d ∨ b = c ∨ b = d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases h with h | h | h | h
  · subst h
    exact Or.inl ⟨rfl, collision_forces_pair
      hK S h2L hLK hprim hP2 hab hcd hvab hvcd rfl⟩
  · subst h
    refine Or.inr ⟨rfl, ?_⟩
    have hne : a ≠ c := fun hh => hcd (hh ▸ rfl)
    exact three_starts_ne hK S h2L hLK hprim hP2 hvab hvcd.symm hab hne
  · subst h
    refine Or.inr ⟨?_, rfl⟩
    have hne : b ≠ d := fun hh => hcd hh
    exact three_starts_ne hK S h2L hLK hprim hP2 hvab.symm hvcd hab.symm hne
  · subst h
    refine Or.inl ⟨?_, rfl⟩
    have hne : b ≠ c := fun hh => hcd hh.symm
    exact three_starts_ne hK S h2L hLK hprim hP2 hvab.symm hvcd.symm hab.symm hne

/-- **§5 step 4, guarded, at an arbitrary alphabet.**  This is
`Issue94Step4Prop.step4_guarded` (`:153`) with its `Bin` binder removed. It is
*the same argument*: the proof body is the α-general
`Issue94IterSlide.step4_slide_iterates_word` at `t ≤ K`, and the `t ≤ K` bound
comes from the α-general `pairBack_spec hK S a b).2` (which is what
`Issue94Step4Prop.pairBack_le_K` is). -/
theorem step4_guarded_alpha (hK : 0 < K) (S : Fin K → α)
    (a b c d : Fin K)
    (hI : Interleaved (mkGenome hK S) a b c d) (t : ℕ) (ht : t ≤ pairBack hK S c.val d.val)
    (hg : ∀ j : ℕ, j ≤ t → SlideGuards hK a b c d j) :
    Interleaved (mkGenome hK S) a b (rotAdd hK (K - t) c) (rotAdd hK (K - t) d) := by
  have _hKne : NeZero K := ⟨hK.ne'⟩
  have htK : t ≤ K := le_trans ht (pairBack_spec hK S c.val d.val).2
  exact step4_slide_iterates_word hK a b c d hI t htK hg

/-! ## 5. A guard failure forces a cross-head equality -/

theorem slide_meets_head_alpha (hK : 0 < K) (S : Fin K → α)
    (h2L : 2 ≤ L) (hLK : L ≤ K)
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
    slide_pair_ne_alpha hK S hcd j
  have hvcd' : vtx hK L S (rotAdd hK (K - j) c) = vtx hK L S (rotAdd hK (K - j) d) :=
    chord_of_slide_alpha hK S hvcd j hj
  have key : (x = rotAdd hK (K - j) c ∧ y = rotAdd hK (K - j) d) ∨
      (x = rotAdd hK (K - j) d ∧ y = rotAdd hK (K - j) c) := by
    rcases h with h | h
    · subst h
      exact step3_shared_endpoint_alpha hK S h2L hLK hP2 hprim
        hxy hcd' hvxy hvcd' (Or.inl rfl)
    · subst h
      exact step3_shared_endpoint_alpha hK S h2L hLK hP2 hprim
        hxy hcd' hvxy hvcd' (Or.inr (Or.inl rfl))
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (by rw [h1, h2])
  · exact Or.inr (by rw [h2, h1])

/-! ## 6. The slide guards, discharged from the cross-head inequalities -/

theorem slide_guards_down_alpha (hK : 0 < K) (S : Fin K → α)
    (h2L : 2 ≤ L) (hLK : L ≤ K)
    (hP2 : P2 hK L S) (hprim : RepeatAdapter.IsPrimitive hK S)
    {a b c d : Fin K} (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d)
    (hAC : maxPairStart hK S a b ≠ maxPairStart hK S c d)
    (hBC : maxPairStart hK S b a ≠ maxPairStart hK S c d) :
    ∀ j : ℕ, j ≤ pairBack hK S c.val d.val → SlideGuards hK a b c d j := by
  intro j hj
  have hCj : maxPairStart hK S (rotAdd hK (K - j) c) (rotAdd hK (K - j) d)
      = maxPairStart hK S c d := head_of_slide_alpha hK S hprim hcd j hj
  have g1 : rotAdd hK (K - j) c ≠ a := by
    intro h
    rcases slide_meets_head_alpha hK S h2L hLK hP2 hprim hcd hab hvcd hvab j hj (Or.inl h) with
      hq | hq
    · exact hAC (by rw [← hCj, hq])
    · exact hBC (by rw [← hCj, hq])
  have g2 : rotAdd hK (K - j) c ≠ b := by
    intro h
    rcases slide_meets_head_alpha hK S h2L hLK hP2 hprim hcd hab.symm hvcd hvab.symm j hj
      (Or.inl h) with hq | hq
    · exact hBC (by rw [← hCj, hq])
    · exact hAC (by rw [← hCj, hq])
  have g3 : rotAdd hK (K - j) d ≠ a := by
    intro h
    rcases slide_meets_head_alpha hK S h2L hLK hP2 hprim hcd hab hvcd hvab j hj (Or.inr h) with
      hq | hq
    · exact hAC (by rw [← hCj, hq])
    · exact hBC (by rw [← hCj, hq])
  have g4 : rotAdd hK (K - j) d ≠ b := by
    intro h
    rcases slide_meets_head_alpha hK S h2L hLK hP2 hprim hcd hab.symm hvcd hvab.symm j hj
      (Or.inr h) with hq | hq
    · exact hBC (by rw [← hCj, hq])
    · exact hAC (by rw [← hCj, hq])
  exact ⟨g1, g2, g3, g4⟩

theorem slide_guards_down_heads_alpha (hK : 0 < K) (S : Fin K → α)
    (h2L : 2 ≤ L) (hLK : L ≤ K)
    (hP2 : P2 hK L S) (hprim : RepeatAdapter.IsPrimitive hK S)
    {a b c d : Fin K} (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d)
    (hAC : maxPairStart hK S a b ≠ maxPairStart hK S c d)
    (hAD : maxPairStart hK S a b ≠ maxPairStart hK S d c)
    (hBC : maxPairStart hK S b a ≠ maxPairStart hK S c d)
    (hBD : maxPairStart hK S b a ≠ maxPairStart hK S d c) :
    ∀ j : ℕ, j ≤ pairBack hK S a.val b.val →
      SlideGuards hK (maxPairStart hK S c d) (maxPairStart hK S d c) a b j := by
  have hCDne : maxPairStart hK S c d ≠ maxPairStart hK S d c :=
    heads_ne_of_chord hK S h2L hLK hprim hcd ((vtx_eq_iff hK S).mp hvcd)
  have hCD : vtx hK L S (maxPairStart hK S c d) = vtx hK L S (maxPairStart hK S d c) :=
    vtx_maxPairStart hK S h2L hLK hprim hcd ((vtx_eq_iff hK S).mp hvcd)
  have hh1 : maxPairStart hK S (maxPairStart hK S c d) (maxPairStart hK S d c)
      = maxPairStart hK S c d := (head_of_head_alpha hK S hprim hcd).1
  have hh2 : maxPairStart hK S (maxPairStart hK S d c) (maxPairStart hK S c d)
      = maxPairStart hK S d c := (head_of_head_alpha hK S hprim hcd).2
  intro j hj
  have hAj : maxPairStart hK S (rotAdd hK (K - j) a) (rotAdd hK (K - j) b)
      = maxPairStart hK S a b := head_of_slide_alpha hK S hprim hab j hj
  have hj2 : j ≤ pairBack hK S b.val a.val := by rw [pairBack_comm]; exact hj
  have hBj : maxPairStart hK S (rotAdd hK (K - j) b) (rotAdd hK (K - j) a)
      = maxPairStart hK S b a := head_of_slide_alpha hK S hprim hab.symm j hj2
  have g1 : rotAdd hK (K - j) a ≠ maxPairStart hK S c d := by
    intro h
    rcases slide_meets_head_alpha hK S h2L hLK hP2 hprim hab hCDne hvab hCD j hj (Or.inl h) with
      hq | hq
    · exact hAC (by rw [← hAj, hq, hh1])
    · exact hAD (by rw [← hAj, hq, hh2])
  have g2 : rotAdd hK (K - j) a ≠ maxPairStart hK S d c := by
    intro h
    have hCD2 : vtx hK L S (maxPairStart hK S d c) = vtx hK L S (maxPairStart hK S c d) :=
      hCD.symm
    have hCDne2 : maxPairStart hK S d c ≠ maxPairStart hK S c d := Ne.symm hCDne
    rcases slide_meets_head_alpha hK S h2L hLK hP2 hprim hab hCDne2 hvab hCD2 j hj (Or.inl h) with
      hq | hq
    · exact hAD (by rw [← hAj, hq, hh2])
    · exact hAC (by rw [← hAj, hq, hh1])
  have g3 : rotAdd hK (K - j) b ≠ maxPairStart hK S c d := by
    intro h
    rcases slide_meets_head_alpha hK S h2L hLK hP2 hprim hab.symm hCDne hvab.symm hCD j hj2
      (Or.inl h) with hq | hq
    · exact hBC (by rw [← hBj, hq, hh1])
    · exact hBD (by rw [← hBj, hq, hh2])
  have g4 : rotAdd hK (K - j) b ≠ maxPairStart hK S d c := by
    intro h
    have hCD2 : vtx hK L S (maxPairStart hK S d c) = vtx hK L S (maxPairStart hK S c d) :=
      hCD.symm
    have hCDne2 : maxPairStart hK S d c ≠ maxPairStart hK S c d := Ne.symm hCDne
    rcases slide_meets_head_alpha hK S h2L hLK hP2 hprim hab.symm hCDne2 hvab.symm hCD2 j hj2
      (Or.inl h) with hq | hq
    · exact hBD (by rw [← hBj, hq, hh2])
    · exact hBC (by rw [← hBj, hq, hh1])
  exact ⟨g1, g2, g3, g4⟩

/-! ## 7. The refuted case, at an arbitrary alphabet -/

/-- **The four cross-head INEQUALITIES force the heads to interleave**, for an
arbitrary `[DecidableEq α]`.  The α-general form of
`Issue94NoCollision.no_collision_heads_interleave`; same argument, `Bin` binding
removed. -/
theorem no_collision_heads_interleave_alpha     (hK : 0 < K) (S : Fin K → α)
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
  have hg1 : ∀ j : ℕ, j ≤ pairBack hK S c.val d.val → SlideGuards hK a b c d j :=
    slide_guards_down_alpha hK S h2L hLK hP2 hprim hab hcd hvab hvcd hAC hBC
  have h1 : Interleaved (mkGenome hK S) a b
      (maxPairStart hK S c d) (maxPairStart hK S d c) := by
    have h1' := step4_guarded_alpha hK S a b c d hI
      (pairBack hK S c.val d.val) (le_refl _) hg1
    convert h1' using 1
    · exact maxPairStart_eq hK S c d
    · rw [pairBack_comm]; exact maxPairStart_eq hK S d c
  have hCDne : maxPairStart hK S c d ≠ maxPairStart hK S d c :=
    heads_ne_of_chord hK S h2L hLK hprim hcd ((vtx_eq_iff hK S).mp hvcd)
  have hCD : vtx hK L S (maxPairStart hK S c d) = vtx hK L S (maxPairStart hK S d c) :=
    vtx_maxPairStart hK S h2L hLK hprim hcd ((vtx_eq_iff hK S).mp hvcd)
  have hg2 : ∀ j : ℕ, j ≤ pairBack hK S a.val b.val →
      SlideGuards hK (maxPairStart hK S c d) (maxPairStart hK S d c) a b j :=
    slide_guards_down_heads_alpha hK S h2L hLK hP2 hprim hab hcd hvab hvcd hAC hAD hBC hBD
  have h2 : Interleaved (mkGenome hK S)
      (maxPairStart hK S c d) (maxPairStart hK S d c)
      (rotAdd hK (K - pairBack hK S a.val b.val) a)
      (rotAdd hK (K - pairBack hK S a.val b.val) b) :=
    step4_guarded_alpha hK S (maxPairStart hK S c d) (maxPairStart hK S d c) a b
      (interleaved_pair_swap hK a b (maxPairStart hK S c d) (maxPairStart hK S d c) h1)
      (pairBack hK S a.val b.val) (le_refl _) hg2
  have hslide : Interleaved (mkGenome hK S)
      (maxPairStart hK S c d) (maxPairStart hK S d c)
      (maxPairStart hK S a b) (maxPairStart hK S b a) := by
    convert h2 using 1
    · exact maxPairStart_eq hK S a b
    · rw [pairBack_comm]; exact maxPairStart_eq hK S b a
  exact interleaved_pair_swap hK (maxPairStart hK S c d) (maxPairStart hK S d c)
    (maxPairStart hK S a b) (maxPairStart hK S b a) hslide

/-- **Closing by `P2.imp_ExtCrossing`, for an arbitrary alphabet.**  The
α-general form of `Issue94NoCollision.no_collision_contradiction`. Head
distinctness is the α-general `heads_ne_of_chord`, not the `Bin`-only
`heads_of_one_chord_ne`, as 94d4's E11 anticipated. -/
theorem no_collision_contradiction_alpha     (hK : 0 < K) (S : Fin K → α)
    (h2L : 2 ≤ L) (hLK : L ≤ K) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) {a b c d : Fin K}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d)
    (hI : Interleaved (mkGenome hK S) a b c d)
    (hAC : maxPairStart hK S a b ≠ maxPairStart hK S c d)
    (hAD : maxPairStart hK S a b ≠ maxPairStart hK S d c)
    (hBC : maxPairStart hK S b a ≠ maxPairStart hK S c d)
    (hBD : maxPairStart hK S b a ≠ maxPairStart hK S d c) : False := by
  have hhAB := head_of_head_alpha hK S hprim hab
  have hhCD := head_of_head_alpha hK S hprim hcd
  have hAB : vtx hK L S (maxPairStart hK S a b) = vtx hK L S (maxPairStart hK S b a) :=
    vtx_maxPairStart hK S h2L hLK hprim hab ((vtx_eq_iff hK S).mp hvab)
  have hCD : vtx hK L S (maxPairStart hK S c d) = vtx hK L S (maxPairStart hK S d c) :=
    vtx_maxPairStart hK S h2L hLK hprim hcd ((vtx_eq_iff hK S).mp hvcd)
  have hneAB := heads_ne_of_chord hK S h2L hLK hprim hab ((vtx_eq_iff hK S).mp hvab)
  have hneCD := heads_ne_of_chord hK S h2L hLK hprim hcd ((vtx_eq_iff hK S).mp hvcd)
  have hcross : Interleaved (mkGenome hK S)
      (maxPairStart hK S a b) (maxPairStart hK S b a)
      (maxPairStart hK S c d) (maxPairStart hK S d c) :=
    no_collision_heads_interleave_alpha hK S h2L hLK hP2 hprim hab hcd hvab hvcd
      hI hAC hAD hBC hBD
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
  exact ((P2.imp_ExtCrossing hK h2L hLK S hprim hP2
    (maxPairStart hK S a b) (maxPairStart hK S b a)
    (maxPairStart hK S c d) (maxPairStart hK S d c)
    hneAB hneCD hAB hCD hcross).1) hIhh

end AssemblyP1.Issue94NoCollisionAlpha
