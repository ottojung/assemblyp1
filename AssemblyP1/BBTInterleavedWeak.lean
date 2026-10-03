import AssemblyP1.BBTInterleavedAdmissible

/-!
# 94b11 — the **weakest hypothesis** for step 4 of the #94 endgame

94a09 (`078d2b7`) proved `selectedInterleaved_admissible` under
`2 ≤ L ∧ IsPrimitive hG S ∧ ¬ LongObstruction hG L S`, and stated in prose
(§3 of its report) that the weakest hypothesis actually needed is

> only that the shift between the two selected starts of the blocked
> constituent is not a period

without claiming that this weaker hypothesis is sufficient.  This module
proves exactly that claim, and identifies the hypothesis precisely.

## The hypothesis, in the project's own terms

`NotPeriodShift hG S a b` = `¬ ShiftInvariant hG S ((b.val + G - a.val) % G)`,
i.e. the shift carrying the start `a` to the start `b` is **not** a period of
the circular word (`RepeatAdapter.ShiftInvariant` is the project's notion of
period-ness by a shift).  This is exactly the shift that
`RepeatAdapter.not_primitive_of_ge_G_agree` produces when two starts agree on
a full turn, so `NotPeriodShift` is precisely the negation of the *single*
consequence of primitivity that the argument consumes.

Two facts, both proved below at general `G`:

* `shiftInvariant_of_agrees_G`: agreement of `a` and `b` on a **full turn**
  forces that shift to be a period.  Hence `NotPeriodShift` is exactly
  "the two copies do **not** agree on a full turn" — nothing weaker is
  available and nothing stronger is needed.
* `isPrimitive_notPeriodShift`: `IsPrimitive hG S → NotPeriodShift hG S a b`,
  so the new theorems below **subsume** 94a09's.

## The discharger

`rightMax_of_doubled_weak` needs, per constituent pair, only the disjunction

```
Preceding a ≠ Preceding b ∨ NotPeriodShift hG S a b
```

because the *unblocked* case is already closed by the library
(`maximalRepeat_of_branch`, no primitivity used at all) and only the blocked
case consumes a period hypothesis.  So the weak hypothesis is needed for the
**blocked constituent only**, exactly as advertised.

`selectedInterleaved_admissible_weak` is the residual implication at general
`G` and general `L`, with the per-quadruple weak hypothesis instead of
`IsPrimitive hG S`.

## Falsification first

A census (`scratch/94b11_census.py`, transcription of the same definitions)
over all unary/binary circular words `G ≤ 8` and `2 ≤ L ≤ 4` finds **no**
instance where the weak hypothesis holds at a selected interleaving but
`AdmissibleObstruction` fails (58256 weak-hypothesis-satisfying quadruples,
0 counterexamples).  Census is evidence, not proof; the theorem is the proof.
No `axiom`, `sorry`, `admit`, `native_decide`, `unsafe` or linter suppression.
-/

namespace AssemblyP1.BBTInterleavedWeak

open SourceFaithfulIs
open AssemblyP1
open AssemblyP1.OrientedRigidity
open AssemblyP1.BBTChords
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerianSearch
open AssemblyP1.BBTSupport
open AssemblyP1.BBTReplacement
open AssemblyP1.BBTAdmissible
open AssemblyP1.BBTInterleaved
open AssemblyP1.RepeatAdapter

variable {α : Type} [DecidableEq α] [Fintype α] {G : ℕ}

/-! ## 1. The weak hypothesis -/

/-- **The shift from `a` to `b` is not a period of the circular word.**
This is the hypothesis §3 of the 94a09 report advertises. -/
def NotPeriodShift (hG : 0 < G) (S : Fin G → α) (a b : Fin G) : Prop :=
  ¬ ShiftInvariant hG S ((b.val + G - a.val) % G)

/-- `cyc` only reads the residue: congruence mod `G` gives equal symbols. -/
theorem cyc_congr_of_mod {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    {x y : ℕ} (h : x % G = y % G) : cyc hG S x = cyc hG S y := by
  have hfin : (⟨x % G, Nat.mod_lt _ hG⟩ : Fin G) = ⟨y % G, Nat.mod_lt _ hG⟩ :=
    Fin.ext h
  unfold cyc
  rw [hfin]

/-- **Agreement on a full turn makes the shift a period.**  So `NotPeriodShift`
is *equivalent* to "the two copies do not agree on a full turn": the weak
hypothesis is exactly as weak as it can be while still excluding the `0101`
obstruction. -/
theorem shiftInvariant_of_agrees_G {α : Type} {G : ℕ} (hG : 0 < G)
    (S : Fin G → α) (a b : Fin G)
    (hag : ∀ d : ℕ, d < G →
      cyc hG S (a.val + d) = cyc hG S (b.val + d)) :
    ShiftInvariant hG S ((b.val + G - a.val) % G) := by
  intro i
  have hdG : (i + G - a.val % G) % G < G := Nat.mod_lt _ hG
  have hAeq : a.val = a.val % G := (Nat.mod_eq_of_lt a.isLt).symm
  have hsh : b.val + G - a.val % G = b.val + G - a.val := by omega
  -- `a.val + offset` reads position `i`
  have hseq1 : (a.val + (i + G - a.val % G) % G) % G = i % G := by
    have h1 : a.val + (i + G - a.val % G) = i + G := by omega
    calc (a.val + (i + G - a.val % G) % G) % G
        = (a.val + (i + G - a.val % G)) % G := Nat.add_mod_mod a.val _ G
      _ = (i + G) % G := by rw [h1]
      _ = i % G := by rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  -- `b.val + offset` reads position `i + shift`
  have hseq2 : (b.val + (i + G - a.val % G) % G) % G =
      (i + (b.val + G - a.val) % G) % G := by
    have h2 : b.val + (i + G - a.val % G) = i + (b.val + G - a.val % G) := by omega
    calc (b.val + (i + G - a.val % G) % G) % G
        = (b.val + (i + G - a.val % G)) % G := Nat.add_mod_mod b.val _ G
      _ = (i + (b.val + G - a.val % G)) % G := by rw [h2]
      _ = (i + (b.val + G - a.val) % G) % G := by
          rw [hsh]
          exact (Nat.add_mod_mod i _ G).symm
  have hag' := hag ((i + G - a.val % G) % G) hdG
  exact (cyc_congr_of_mod hG S hseq1).symm.trans
    (hag'.trans (cyc_congr_of_mod hG S hseq2))

/-- **Primitivity implies the weak hypothesis**, at every pair of starts: the
new theorems subsume 94a09's. -/
theorem isPrimitive_notPeriodShift {α : Type} {G : ℕ} (hG : 0 < G)
    (S : Fin G → α) (hprim : IsPrimitive hG S) {a b : Fin G} (hab : a ≠ b) :
    NotPeriodShift hG S a b := by
  intro hsi
  have hAeq2 : b.val % G = b.val := Nat.mod_eq_of_lt b.isLt
  have hsG : (b.val + G - a.val) % G < G := Nat.mod_lt _ hG
  have hs0 : 0 < (b.val + G - a.val) % G := by
    by_contra hc
    have hzero : (b.val + G - a.val) % G = 0 := Nat.eq_zero_of_not_pos hc
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hzero
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, Nat.mul_zero] at hk
      omega
    · have hk3 : k < 3 := by
        rcases Nat.lt_or_ge k 3 with h | h
        · exact h
        · exfalso
          have h3 : G * 3 ≤ G * k := Nat.mul_le_mul_left G h
          omega
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have hk1 : k = 1 := by omega
        rw [hk1, Nat.mul_one] at hk
        exact absurd (show a.val = b.val by omega) (fun e => hab (Fin.ext e))
      · have h2G : G * 2 ≤ G * k := Nat.mul_le_mul_left G hk2
        omega
  exact hprim _ hs0 hsG hsi

/-- **The weak hypothesis rules out a full turn of agreement.** -/
theorem not_agrees_G_of_notPeriodShift {α : Type} {G : ℕ} (hG : 0 < G)
    (S : Fin G → α) {a b : Fin G} (hH : NotPeriodShift hG S a b) :
    ¬ ∀ d : ℕ, d < G → cyc hG S (a.val + d) = cyc hG S (b.val + d) :=
  fun hag => hH (shiftInvariant_of_agrees_G hG S a b hag)

/-! ## 1b. The weak hypothesis is also **necessary**: it cannot be weakened -/

/-- **Congruence bookkeeping** for the shift `((b + G - a) % G)`. -/
theorem shift_residue {G : ℕ} (a b e : Fin G) :
    (a.val + e.val + (b.val + G - a.val) % G) % G = (b.val + e.val) % G := by
  have h1 : a.val + (b.val + G - a.val) = b.val + G := by
    have : a.val ≤ b.val + G := by omega
    omega
  calc (a.val + e.val + (b.val + G - a.val) % G) % G
      = ((a.val + e.val) + (b.val + G - a.val)) % G := Nat.add_mod_mod _ _ _
    _ = (e.val + (a.val + (b.val + G - a.val))) % G := by congr 1; omega
    _ = (e.val + (b.val + G)) % G := by rw [h1]
    _ = (e.val + b.val + G) % G := by congr 1; omega
    _ = (b.val + e.val + G) % G := by congr 1; omega
    _ = (b.val + e.val) % G := by
        rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]

/-- **If the shift between `a` and `b` *is* a period, there is no right-maximal
repeat at those two starts at all** --- hence no admissible obstruction can use
them as a constituent, blocked or not.  So `NotPeriodShift` is not merely
sufficient but *necessary*, and 94a09's `no_rightRepeat_0101` is the concrete
instance of this at `S = 0101`. -/
theorem no_rightRepeat_of_periodShift {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G)
    (S : Fin G → α) {a b : Fin G}
    (hsi : ShiftInvariant hG S ((b.val + G - a.val) % G)) :
    ¬ ∃ e : Fin G, IsRightRepeat hG S e a b := by
  rintro ⟨e, h⟩
  refine h.2.2.2 ?_
  have h1 : cyc hG S (a.val + e.val) = cyc hG S (a.val + e.val
      + (b.val + G - a.val) % G) := hsi (a.val + e.val)
  have h2 : cyc hG S (b.val + e.val) = cyc hG S (a.val + e.val
      + (b.val + G - a.val) % G) :=
    cyc_congr_of_mod hG S (shift_residue (G := G) a b e).symm
  simpa only [SourceFaithfulIs.Genome.Following, cycl_mkGenome] using
    h1.trans h2.symm

/-! ## 2. The lemma the residual needs, in the weak form -/

/-- **Weak form of `BBTInterleaved.rightMax_of_doubled`.**  Every doubled
`(L-1)`-mer whose two starts either have different preceding symbols or are
joined by a non-period shift extends, *at the same two starts*, to a
right-maximal repeat of length `≥ L - 1`.

No primitivity anywhere.  The unblocked case is the library's
`maximalRepeat_of_branch`; the blocked case uses the maximal *right*
extension at the same two starts, and the only way it can fail is a full turn
of agreement, i.e. a period shift, excluded by `NotPeriodShift`. -/
theorem rightMax_of_doubled_weak {α : Type} [DecidableEq α] {G : ℕ}
    (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    {a b : Fin G} (hL : 2 ≤ L) (hab : a ≠ b)
    (hvt : vtx hG L S a = vtx hG L S b)
    (hH : (mkGenome hG S).Preceding a ≠ (mkGenome hG S).Preceding b ∨
      NotPeriodShift hG S a b) :
    ∃ e : Fin G, L - 1 ≤ e.val ∧ IsRightRepeat hG S e a b := by
  have hK1 : 1 ≤ L - 1 := by omega
  have hag : Agrees hG S (L - 1) a b := fun d => congrFun hvt d
  by_cases hprec : (mkGenome hG S).Preceding a = (mkGenome hG S).Preceding b
  · -- blocked: the weak hypothesis must be the right disjunct
    have hH' : NotPeriodShift hG S a b := by
      rcases hH with h | h
      · exact (h hprec).elim
      · exact h
    -- a full turn of agreement is excluded, so `L - 1 < G`
    have hlt : L - 1 < G := by
      by_contra hc
      exact hH' (shiftInvariant_of_agrees_G hG S a b
        (fun d hd => hag ⟨d, by omega⟩))
    let T : Finset ℕ := Finset.range G |>.filter
      (fun r => ∀ d : ℕ, d < r → cyc hG S (a.val + d) = cyc hG S (b.val + d))
    have hne : T.Nonempty :=
      ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        fun d hd => by omega⟩⟩
    have hmemL : L - 1 ∈ T :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt,
        fun d hd => hag ⟨d, hd⟩⟩
    have hrT : T.max' hne ∈ T := Finset.max'_mem _ hne
    have hrG : T.max' hne < G := Finset.mem_range.mp (Finset.mem_filter.mp hrT).1
    have hrag : ∀ d : ℕ, d < T.max' hne → cyc hG S (a.val + d) = cyc hG S (b.val + d) :=
      (Finset.mem_filter.mp hrT).2
    have hge : L - 1 ≤ T.max' hne := Finset.le_max' _ _ hmemL
    have hFoll : cyc hG S (a.val + T.max' hne) ≠ cyc hG S (b.val + T.max' hne) := by
      intro hc
      by_cases hlt1 : T.max' hne + 1 < G
      · have hr1 : T.max' hne + 1 ∈ T := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt1, ?_⟩
          intro d hd
          rcases Nat.lt_or_ge d (T.max' hne) with h | h
          · exact hrag d h
          · have hd' : d = T.max' hne := by omega
            simpa only [hd', Nat.add_zero] using hc
        exact absurd (Finset.le_max' _ _ hr1) (by omega)
      · have hlen : T.max' hne + 1 = G := by omega
        have hG_ag : ∀ d : ℕ, d < G →
            cyc hG S (a.val + d) = cyc hG S (b.val + d) := by
          intro d hd
          rcases Nat.lt_trichotomy d (T.max' hne) with h | h | h
          · exact hrag d h
          · subst h
            simpa only [hlen, Nat.add_zero] using hc
          · omega
        exact hH' (shiftInvariant_of_agrees_G hG S a b hG_ag)
    have h1r : 1 ≤ T.max' hne := by omega
    refine ⟨⟨T.max' hne, hrG⟩, hge, ⟨h1r, ?_, hab, ?_⟩⟩
    · intro d
      exact hrag d.val d.isLt
    · simpa only [SourceFaithfulIs.Genome.Following, cycl_mkGenome] using hFoll
  · -- unblocked: the library's maximal repeat, no hypothesis consumed
    obtain ⟨e, he, hlen⟩ := maximalRepeat_of_branch (α := α) hG S hL hab hvt hprec
    exact ⟨e, hlen, ⟨he.1, he.2.2.2.1, he.2.2.1, he.2.2.2.2.2⟩⟩

/-! ## 3. The residual implication, at general `G` and general `L` -/

/-- **The weak hypothesis of §2, stated for one interleaving quadruple.**
It constrains only the two shifts and only at interleaved quadruples; nothing
else about the genome is required. -/
def WeakInterleavingHyp (hG : 0 < G) (S : Fin G → α) (a b c d : Fin G) : Prop :=
  ((mkGenome hG S).Preceding a ≠ (mkGenome hG S).Preceding b ∨
      NotPeriodShift hG S a b) ∧
    ((mkGenome hG S).Preceding c ≠ (mkGenome hG S).Preceding d ∨
      NotPeriodShift hG S c d)

/-! ## 3. The residual implication, at general `G` and general `L` -/
/-- **The residual, in the weakest hypothesis.**  A selected interleaving of a
genome with no long obstruction, whose every interleaved pair of doubled
`(L-1)`-mers is either unblocked or joined by a non-period shift, is an
admissible obstruction.

This **strictly weakens** `selectedInterleaved_admissible`: primitivity of the
word implies the per-pair hypothesis by `isPrimitive_notPeriodShift`
(`selectedInterleaved_admissible_weak_of_primitive` below), but it is required
only of the pairs that are actually preceding-blocked, and only at one shift
each. -/
theorem selectedInterleaved_admissible_weak
    (hG : 0 < G) (L : ℕ) (S : Fin G → α) {θ : Fin G → Fin G} (hL : 2 ≤ L)
    (hS : SelectedInterleaved hG L S θ)
    (hno : ¬ LongObstruction hG L S)
    (hW : ∀ a b c d : Fin G, Interleaved (mkGenome hG S) a b c d →
      WeakInterleavingHyp hG S a b c d) :
    AdmissibleObstruction hG L S := by
  obtain ⟨a, b, c, d, hIA, hva, hvc, hblk⟩ :=
    selectedInterleaved_crux (α := α) hG L S hL hS hno
  have hIA' := (interleaved_iff_interleavedStarts hG S a b c d).mp hIA
  obtain ⟨hH1, hH2⟩ := hW a b c d hIA'
  obtain ⟨e₁, hlen₁, hrr₁⟩ :=
    rightMax_of_doubled_weak hG L S hL hIA.1.1 hva hH1
  obtain ⟨e₂, hlen₂, hrr₂⟩ :=
    rightMax_of_doubled_weak hG L S hL hIA.1.2.2.2.2.2 hvc hH2
  refine ⟨e₁, e₂, a, b, c, d,
    (interleaved_iff_interleavedStarts hG S a b c d).mp hIA,
    hlen₁, hlen₂, hrr₁, hrr₂, ?_⟩
  rcases hblk with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **94a09's theorem is a special case**: the weak hypothesis is implied by
primitivity, so nothing is lost. -/
theorem selectedInterleaved_admissible_weak_of_primitive
    (hG : 0 < G) (L : ℕ) (S : Fin G → α) {θ : Fin G → Fin G} (hL : 2 ≤ L)
    (hprim : IsPrimitive hG S)
    (hS : SelectedInterleaved hG L S θ)
    (hno : ¬ LongObstruction hG L S) :
    AdmissibleObstruction hG L S := by
  have hW : ∀ a b c d : Fin G, Interleaved (mkGenome hG S) a b c d →
      WeakInterleavingHyp hG S a b c d := by
    intro a b c d hIA
    have hab : a ≠ b := hIA.1.1
    have hcd : c ≠ d := hIA.1.2.2.2.2.2
    refine ⟨Or.inr (isPrimitive_notPeriodShift hG S hprim hab), ?_⟩
    exact Or.inr (isPrimitive_notPeriodShift hG S hprim hcd)
  apply selectedInterleaved_admissible_weak (α := α) hG L S hL hS hno
  exact hW

/-! ## 4. Non-vacuity: the weak hypothesis is inhabited, and its *blocked*
disjunct is genuinely needed -/

/-- At `00101` (`G = 5`, `L = 3`) the pair `(2, 4)` is **preceding-blocked**
(`Preceding 2 = Preceding 4 = 0`), so the left disjunct of the weak hypothesis
fails there: the non-period hypothesis is not decorative. -/
theorem blocked_00101 : (mkGenome BBTChords.hG5 BBTReplacement.S5b).Preceding 2 =
    (mkGenome BBTChords.hG5 BBTReplacement.S5b).Preceding 4 := by decide

/-- ... and the shift from `2` to `4` is nevertheless not a period, since
`00101` is primitive (`BBTInterleaved.primitive_00101`). -/
theorem notPeriodShift_2_4_00101 :
    NotPeriodShift BBTChords.hG5 BBTReplacement.S5b 2 4 :=
  isPrimitive_notPeriodShift BBTChords.hG5 BBTReplacement.S5b
    BBTInterleaved.primitive_00101 (by decide)

/-- **Non-vacuity, kernel-checked.**  The hypothesis set of
`selectedInterleaved_admissible_weak` is inhabited, and at the witnessing
quadruple `(1, 3, 2, 4)` *both* disjuncts occur: the first pair is unblocked
and the second is blocked with a non-period shift.  `¬ LongObstruction` and
`AdmissibleObstruction` hold at the same genome (`BBTReplacement.not_longObstruction_00101`,
`BBTAdmissible.admissible_00101`), and the selected interleaving is
`BBTInterleaved.selectedInterleaved_00101`.  So the theorem is not vacuously
true, and the weaker hypothesis is not vacuous. -/
theorem weak_hypotheses_inhabited_00101 :
    ¬ LongObstruction BBTChords.hG5 3 BBTReplacement.S5b ∧
      (∃ θ : Fin 5 → Fin 5,
        Function.Bijective θ ∧
          FibrePreserving (hG := BBTChords.hG5) (L := 3) BBTReplacement.S5b θ ∧
          OneCycle BBTChords.hG5 θ ∧
          SelectedInterleaved (hG := BBTChords.hG5) (L := 3)
            BBTReplacement.S5b θ) ∧
      AdmissibleObstruction (hG := BBTChords.hG5) (L := 3) BBTReplacement.S5b ∧
      Interleaved (mkGenome BBTChords.hG5 BBTReplacement.S5b) 1 3 2 4 ∧
      WeakInterleavingHyp BBTChords.hG5 BBTReplacement.S5b 1 3 2 4 := by
  refine ⟨BBTReplacement.not_longObstruction_00101,
    BBTInterleaved.selectedInterleaved_00101, BBTAdmissible.admissible_00101, ?_, ?_⟩
  · exact (BBTInterleaved.interleaved_iff_interleavedStarts BBTChords.hG5
      BBTReplacement.S5b 1 3 2 4).mpr (by decide)
  · exact ⟨Or.inl (by decide), Or.inr notPeriodShift_2_4_00101⟩

end AssemblyP1.BBTInterleavedWeak