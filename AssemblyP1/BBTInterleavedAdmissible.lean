import AssemblyP1.BBTAdmissibleObstruction

/-!
# `SelectedInterleaved ⟹ AdmissibleObstruction` (front 94a09)

The live residual named in `/workspace/BOARD94-ENDGAME-1000.md` §6 step 4.

Two results, in this order, because the first is the falsification of the
statement as written and the second is the strongest correct form.

## 1. The unconditional statement is FALSE, kernel-checked

`selectedInterleaved_admissible_unconditional_false` exhibits `S = 0101`,
`G = 4`, `L = 3` and the swapping successor `θ = (0 2)(1 3)`, and proves

```
SelectedInterleaved θ  ⟹  AdmissibleObstruction   is false there
```

The instance is a `P2` genome (`p2_0101_L3`), so it is also a counterexample
to the `P2`-strengthened statement, and `¬ LongObstruction` holds there as
well (`not_longObstruction_0101`).  The cause is named and proved: the genome
is **non-primitive** (`not_primitive_0101`), and at a period-`2` word every
pair of distinct starts that agrees at all is a shift by the period, at which
the two copies never diverge to the right (`no_rightRepeat_0101`, and
`agree_0101_preceding`, which is the same fact read on the left).  So no
right-maximal repeat of length `≥ L - 1` exists at all, while the two doubled
`(L-1)`-mers do interleave and are both selected.

## 2. The strongest correct form, proved

`rightMax_of_doubled`: **every** doubled `(L-1)`-mer of a *primitive* genome
extends, *at the same two starts*, to a right-maximal repeat of length
`≥ L - 1`.  No case split in the caller and no `Preceding`-hypothesis: when
the two preceding symbols differ this is
`BBTMaximalExtension.maximalRepeat_of_branch`, and when they coincide the
maximal *right* extension exists because a full turn of agreement contradicts
primitivity (`RepeatAdapter.not_primitive_of_ge_G_agree`).

`selectedInterleaved_admissible`: the residual implication, at general `G`
and general `L`, under the three hypotheses the endgame actually has ---
`2 ≤ L`, primitivity of the truth, and `¬ LongObstruction` --- and
`selectedInterleaved_admissible_of_P2`, the same statement with
`¬ LongObstruction` replaced by `P2` (the two are equivalent at `2 ≤ L` by
`BBTReplacement.longObstruction_iff_not_P2`).

`AdmissibleObstruction` appears here only as a **conclusion**; it is never a
hypothesis, and `P2` is used only through its `¬ LongObstruction` equivalent.

## 3. Non-vacuity of the statement proved in §4

`hypotheses_inhabited_00101`: the hypothesis set of §4 is inhabited ---
`00101` is primitive (`primitive_00101`), has no long obstruction, and admits
a bijective, fibre-preserving, one-cycle `θ` that is selected-interleaved
(`selectedInterleaved_00101`, the instance the library already records as
`BBTSupport.harmless_selected_crossing_00101`).  `AdmissibleObstruction` then
holds there, as `admissible_00101` records independently.

## 4. What is NOT proved here

The discharger itself (`P2 ∧ bad θ ∧ ¬ SelectedTriple θ ∧ SelectedInterleaved
θ → False`, step 5 of §6 of `/workspace/BOARD94-ENDGAME-1000.md`) is untouched;
so are `SupportDichotomy` and the primitivity lemma of step 3 of the same
section (which is about `(L-1)`-mers of multiplicity `≥ 3`, a different
statement from the primitivity *of the word* used here).  No `axiom`, `sorry`,
`admit`, `native_decide`, `unsafe` or linter suppression occurs in this file.
-/

namespace AssemblyP1.BBTInterleaved

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
open AssemblyP1.RepeatAdapter


/-! ## 3. The lemma the residual needs: right-maximal extension *at the same
starts*, for a primitive genome -/

/-- **Doubled `(L-1)`-mers of a primitive genome extend to right-maximal
repeats at the same two starts, of length `≥ L - 1`.**

This is the piece the endgame report (`/workspace/BOARD94-ENDGAME-1000.md`
§6 step 4) names as missing.  The genome-side `Preceding` clause of
`maximalRepeat_of_branch` is *circular* (94d05/94f01), so it may not be
assumed.  Here the pair is kept at the starts the selection gave, so the
interleaving is preserved, and the blocked case is handled on the right
instead of the left:

* preceding symbols differ: `BBTMaximalExtension.maximalRepeat_of_branch`
  gives a maximal repeat, hence in particular a right-maximal one;
* preceding symbols coincide: agreement extends to the left, so the maximal
  **right** extension `r` at the same two starts exists and is `< G`, and the
  two following symbols differ there.

The bound `L - 1 < G` is not assumed: it follows from primitivity, because
two distinct starts agreeing on `≥ G` positions make `S` shift-invariant
(`RepeatAdapter.not_primitive_of_ge_G_agree`). -/
theorem rightMax_of_doubled {α : Type} [DecidableEq α] [Fintype α] {G : ℕ}
    (hG : 0 < G) (L : ℕ) (S : Fin G → α) {a b : Fin G} (hL : 2 ≤ L) (hab : a ≠ b)
    (hvt : vtx hG L S a = vtx hG L S b)
    (hprim : IsPrimitive hG S) :
    ∃ e : Fin G, L - 1 ≤ e.val ∧ IsRightRepeat hG S e a b := by
  have hK1 : 1 ≤ L - 1 := by omega
  have hag : Agrees hG S (L - 1) a b := fun d => congrFun hvt d
  have hAB : a.val % G ≠ b.val % G := by
    intro h
    exact hab (Fin.ext ((Nat.mod_eq_of_lt a.isLt).symm.trans
      (h.trans (Nat.mod_eq_of_lt b.isLt))))
  -- primitivity bounds the agreement below a full turn
  have hlt : L - 1 < G := by
    by_contra hc
    exact not_primitive_of_ge_G_agree hG S a.val b.val (L - 1) hAB (by omega)
      (fun d hd => hag ⟨d, hd⟩) hprim
  by_cases hprec : (mkGenome hG S).Preceding a = (mkGenome hG S).Preceding b
  · -- the blocked case: maximal *right* extension at the same two starts
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
      · -- extend by one symbol: contradicts the maximality of `r`
        have hr1 : T.max' hne + 1 ∈ T := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt1, ?_⟩
          intro d hd
          rcases Nat.lt_or_ge d (T.max' hne) with h | h
          · exact hrag d h
          · have hd' : d = T.max' hne := by omega
            simpa only [hd', Nat.add_zero] using hc
        exact absurd (Finset.le_max' _ _ hr1) (by omega)
      · -- `r + 1 = G`: a full turn of agreement, i.e. non-primitivity
        have hlen : T.max' hne + 1 = G := by omega
        have hG_ag : ∀ d : ℕ, d < G →
            cyc hG S (a.val + d) = cyc hG S (b.val + d) := by
          intro d hd
          rcases Nat.lt_trichotomy d (T.max' hne) with h | h | h
          · exact hrag d h
          · subst h
            simpa only [hlen, Nat.add_zero] using hc
          · omega
        exact (not_primitive_of_ge_G_agree hG S a.val b.val G hAB (le_refl G)
          hG_ag hprim).elim
    have h1r : 1 ≤ T.max' hne := by omega
    refine ⟨⟨T.max' hne, hrG⟩, hge, ⟨h1r, ?_, hab, ?_⟩⟩
    · intro d
      exact hrag d.val d.isLt
    · simpa only [SourceFaithfulIs.Genome.Following, cycl_mkGenome] using hFoll
  · -- the unblocked case: the library's maximal repeat
    obtain ⟨e, he, hlen⟩ := maximalRepeat_of_branch (α := α) hG S hL hab hvt hprec
    exact ⟨e, hlen, ⟨he.1, he.2.2.2.1, he.2.2.1, he.2.2.2.2.2⟩⟩

/-! ## 4. The residual implication, at general `G` and general `L` -/

/-- **`Interleaved` is `InterleavedStarts`**: the two interleaving predicates
of the library are the same predicate (`BBTChords.InArc` and
`Genome.InOpenArc` are the same formula on `mkGenome`), so the four starts
delivered by `selectedInterleaved_crux` are usable as the four starts of
`AdmissibleObstruction` without moving anything.  `Iff.rfl`. -/
theorem interleaved_iff_interleavedStarts {α : Type} [DecidableEq α] {G : ℕ}
    (hG : 0 < G) (S : Fin G → α) (a b c d : Fin G) :
    Interleaved (mkGenome hG S) a b c d ↔ InterleavedStarts hG a b c d := Iff.rfl

/-- **The residual, proved (front 94a09).**  A selected interleaving of a
*primitive* genome with no long obstruction is an admissible obstruction: the
four selected starts interleave, both pairs extend to right-maximal repeats
of length `≥ L - 1` **at those very starts**, and one of the two pairs is
preceding-blocked.

The three hypotheses are exactly the ones the endgame has: `2 ≤ L`,
primitivity of the truth, and `¬ LongObstruction`.  No `θ`-hypothesis is
needed beyond `SelectedInterleaved` itself, and no `AdmissibleObstruction`
appears on the left. -/
theorem selectedInterleaved_admissible {α : Type} [DecidableEq α] [Fintype α]
    {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α) {θ : Fin G → Fin G} (hL : 2 ≤ L)
    (hprim : IsPrimitive hG S)
    (hS : SelectedInterleaved hG L S θ)
    (hno : ¬ LongObstruction hG L S) :
    AdmissibleObstruction hG L S := by
  obtain ⟨a, b, c, d, hIA, hva, hvc, hblk⟩ :=
    selectedInterleaved_crux (α := α) hG L S hL hS hno
  obtain ⟨e₁, hlen₁, hrr₁⟩ :=
    rightMax_of_doubled hG L S hL hIA.1.1 hva hprim
  obtain ⟨e₂, hlen₂, hrr₂⟩ :=
    rightMax_of_doubled hG L S hL hIA.1.2.2.2.2.2 hvc hprim
  refine ⟨e₁, e₂, a, b, c, d,
    (interleaved_iff_interleavedStarts hG S a b c d).mp hIA,
    hlen₁, hlen₂, hrr₁, hrr₂, ?_⟩
  rcases hblk with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **The same statement in the endgame's `P2` form.**  `P2` and
`¬ LongObstruction` are equivalent at `2 ≤ L`
(`BBTReplacement.longObstruction_iff_not_P2`), so this is the residual with
the genome-side hypothesis the endgame actually carries. -/
theorem selectedInterleaved_admissible_of_P2 {α : Type} [DecidableEq α]
    [Fintype α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    {θ : Fin G → Fin G} (hL : 2 ≤ L)
    (hprim : IsPrimitive hG S) (hP2 : P2 hG L S)
    (hS : SelectedInterleaved hG L S θ) :
    AdmissibleObstruction hG L S :=
  selectedInterleaved_admissible hG L S hL hprim hS
    (not_longObstruction_of_P2 (α := α) (hG := hG) (L := L) (S := S) hL hP2)

/-! ## 5. The falsification: `S = 0101`, `G = 4`, `L = 3`, `θ = (0 2)(1 3)` -/

/-- `S = 0101` read on four positions. -/
def S0101 : Fin 4 → Fin 2 := fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1

theorem hG4 : 0 < 4 := by decide

/-- The successor that swaps the two occurrences of each doubled `2`-mer. -/
def swap0101 : Fin 4 → Fin 4 := fun | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1

/-- **The period-`2` arithmetic of `0101`:** reading the circle at any index
returns the index modulo `2`. -/
theorem cyc_0101_raw (i : ℕ) :
    cyc hG4 S0101 i = S0101 ⟨i % 4, Nat.mod_lt _ (by decide)⟩ := rfl

theorem S0101_val (j : Fin 4) : S0101 j = ⟨j.val % 2, by omega⟩ := by
  fin_cases j <;> decide

theorem cyc_0101 (i : ℕ) : (cyc hG4 S0101 i).val = i % 2 := by
  rw [cyc_0101_raw, S0101_val]
  show (i % 4) % 2 = i % 2
  exact Nat.mod_mod_of_dvd i (show 2 ∣ 4 from ⟨2, by decide⟩)

/-- **Equal residues modulo `2` stay equal under a common shift.** -/
theorem mod2_shift {i j k : ℕ} (h : i % 2 = j % 2) : (i + k) % 2 = (j + k) % 2 := by
  calc (i + k) % 2 = ((i % 2) + (k % 2)) % 2 := Nat.add_mod _ _ _
    _ = ((j % 2) + (k % 2)) % 2 := by rw [h]
    _ = (j + k) % 2 := (Nat.add_mod _ _ _).symm

theorem prec_0101 (a : Fin 4) :
    ((mkGenome hG4 S0101).Preceding a).val = (a.val + 4 - 1) % 2 := by
  simpa only [SourceFaithfulIs.Genome.Preceding, len_mkGenome, cycl_mkGenome]
    using cyc_0101 (a.val + (4 : ℕ) - 1)

/-- **On `0101`, agreement at all forces equal preceding symbols.**  Two
distinct starts that agree on `≥ 1` symbol are a shift by the period `2`, so
the copies cannot differ to the left either. -/
theorem agree_0101_preceding {e : ℕ} {a b : Fin 4}
    (h : Agrees hG4 S0101 e a b) (he : 1 ≤ e) :
    (mkGenome hG4 S0101).Preceding a = (mkGenome hG4 S0101).Preceding b := by
  refine Fin.ext ?_
  rw [prec_0101, prec_0101]
  have h1 := h ⟨0, by omega⟩
  simp only [Nat.add_zero] at h1
  have h0 : a.val % 2 = b.val % 2 := by
    have h := congrArg Fin.val h1
    simpa only [cyc_0101] using h
  exact mod2_shift h0

/-- **At `S = 0101` there is no right-maximal repeat of any length.**  Every
pair of distinct starts that agrees on `≥ 1` symbol is a shift by the period
`2`, at which the two copies never diverge to the right.  This is why the
extra hypothesis of §4 is not cosmetic, and it is the same fact
`agree_0101_preceding` reads on the left. -/
theorem no_rightRepeat_0101 :
    ∀ e a b : Fin 4, IsRightRepeat (hG := hG4) (S := S0101) e a b → False := by
  intro e a b h
  have he : 1 ≤ e := h.1
  have h2 := h.2.1 ⟨0, by omega⟩
  simp only [Nat.add_zero] at h2
  have h0 : a.val % 2 = b.val % 2 := by
    have h := congrArg Fin.val h2
    simpa only [cyc_0101] using h
  have hF : cyc hG4 S0101 (a.val + e.val) = cyc hG4 S0101 (b.val + e.val) := by
    refine Fin.ext ?_
    have heq : (a.val + e.val) % 2 = (b.val + e.val) % 2 := mod2_shift h0
    rw [cyc_0101, cyc_0101, heq]
  exact h.2.2.2 (by simpa only [SourceFaithfulIs.Genome.Following, len_mkGenome,
    cycl_mkGenome] using hF)

/-- **Hence no admissible obstruction at `0101`, `L = 3`.** -/
theorem not_admissible_0101 :
    ¬ AdmissibleObstruction (hG := hG4) (L := 3) S0101 := by
  rintro ⟨e₁, e₂, a, b, c, d, _, _, _, hrr₁, _, _⟩
  exact no_rightRepeat_0101 e₁ a b hrr₁

/-- **The selected interleaving at `0101`:** `0, 2` and `1, 3` are the two
doubled `2`-mers, they interleave, and `θ` selects both. -/
theorem selectedInterleaved_0101 :
    SelectedInterleaved (hG := hG4) (L := 3) S0101 swap0101 := by
  refine ⟨0, 2, 1, 3, ?_, ?_, ?_, ⟨0, ?_, ?_⟩, ⟨1, ?_, ?_⟩⟩
  · refine ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide⟩, ?_⟩
    unfold InOpenArc
    decide
  · decide
  · decide
  · exact (mem_fibre (hG := hG4) (L := 3) (S := S0101)).mpr rfl
  · decide
  · exact (mem_fibre (hG := hG4) (L := 3) (S := S0101)).mpr rfl
  · decide

/-- **REFUTATION, kernel-checked: `SelectedInterleaved θ ⟹ AdmissibleObstruction`
is false as stated.**  The hypothesis holds at `0101` with `θ = (0 2)(1 3)`;
the conclusion fails there. -/
theorem selectedInterleaved_admissible_unconditional_false :
    ¬ (SelectedInterleaved (hG := hG4) (L := 3) S0101 swap0101 →
        AdmissibleObstruction (hG := hG4) (L := 3) S0101) :=
  fun h => not_admissible_0101 (h selectedInterleaved_0101)

/-- **No maximal repeat of any length at `0101`:** on a period-`2` word two
distinct starts that agree at all also share their preceding symbol, so
`IsRepeat` is vacuous.  This is what makes the genome `P2`. -/
theorem no_IsRepeat_0101 :
    ∀ (e a b : Fin 4), (mkGenome hG4 S0101).IsRepeat e a b → False := by
  intro e a b h
  exact absurd (agree_0101_preceding h.2.2.2.1 h.1) h.2.2.2.2.1

/-- The counterexample genome is `P2`, so adding `P2` does not rescue the
statement. -/
theorem p2_0101_L3 : P2 hG4 3 S0101 := by
  constructor
  · intro e a b c hT
    by_cases he : e.val < 2
    · exact he
    · have h1 := agree_0101_preceding hT.2.2.2.2.2.1 hT.1
      have h2 := agree_0101_preceding hT.2.2.2.2.2.2.1 hT.1
      exact (hT.2.2.2.2.2.2.2.2.1 ⟨h1, h1.symm.trans h2⟩).elim
  · intro e₁ e₂ a b c d h1 h2 h3
    exact (no_IsRepeat_0101 e₁ a b h1).elim

/-- ... and hence `¬ LongObstruction` holds there too: the residual of §4 fails
at this instance for exactly one reason, `¬ IsPrimitive`. -/
theorem not_longObstruction_0101 : ¬ LongObstruction hG4 3 S0101 :=
  not_longObstruction_of_P2 (by decide) p2_0101_L3

/-- **The named obstruction.**  `0101` is a square, so the extra hypothesis
of §4 is genuinely needed: the implication fails at the non-primitive
genomes. -/
theorem not_primitive_0101 : ¬ IsPrimitive hG4 S0101 := by
  refine fun hprim => hprim 2 (by decide) (by decide) ?_
  intro i
  have h1 : cyc hG4 S0101 i = cyc hG4 S0101 (i + 2) := by
    refine Fin.ext ?_
    rw [cyc_0101, cyc_0101]
    simp
  exact h1

/-! ## 6. Non-vacuity of §4: the hypothesis set is inhabited -/

/-- **`00101` is a primitive word**: no nonzero shift below `5` preserves it. -/
theorem primitive_00101 : IsPrimitive BBTChords.hG5 BBTReplacement.S5b := by
  intro s hs hs5 hsi
  interval_cases s
  all_goals first
    | exact absurd (hsi 0) (by decide)
    | exact absurd (hsi 1) (by decide)

set_option maxRecDepth 1000000 in
/-- **A selected interleaving on the primitive genome `00101`, `L = 3`** --- the
same instance the library records as `BBTSupport.harmless_selected_crossing_00101`
(the word `S5b` of `BBTReplacement` is `![0,0,1,0,1]`, the word of
`BBTChords.S5`). -/
theorem selectedInterleaved_00101 :
    ∃ θ : Fin 5 → Fin 5, Function.Bijective θ ∧
      FibrePreserving (hG := BBTChords.hG5) (L := 3) BBTReplacement.S5b θ ∧
      OneCycle BBTChords.hG5 θ ∧
      SelectedInterleaved (hG := BBTChords.hG5) (L := 3) BBTReplacement.S5b θ := by
  decide

/-- **Non-vacuity, kernel-checked.**  The hypothesis set of
`selectedInterleaved_admissible` is inhabited: `00101` is primitive, has no long
obstruction, and admits a bijective, fibre-preserving, one-cycle `θ` that is
selected-interleaved.  `AdmissibleObstruction` then holds there --- as the
library already records independently in `admissible_00101`.  So §4 is not
vacuously true.

It is **not** claimed that a *bad* such `θ` exists: that is the discharger,
step 5 of §6 of `/workspace/BOARD94-ENDGAME-1000.md`, and it is untouched here.
-/
theorem hypotheses_inhabited_00101 :
    IsPrimitive BBTChords.hG5 BBTReplacement.S5b ∧
      ¬ LongObstruction BBTChords.hG5 3 BBTReplacement.S5b ∧
      (∃ θ : Fin 5 → Fin 5,
        Function.Bijective θ ∧
          FibrePreserving (hG := BBTChords.hG5) (L := 3) BBTReplacement.S5b θ ∧
          OneCycle BBTChords.hG5 θ ∧
          SelectedInterleaved (hG := BBTChords.hG5) (L := 3)
            BBTReplacement.S5b θ) ∧
      AdmissibleObstruction (hG := BBTChords.hG5) (L := 3) BBTReplacement.S5b :=
  ⟨primitive_00101, BBTReplacement.not_longObstruction_00101,
    selectedInterleaved_00101, BBTAdmissible.admissible_00101⟩

end AssemblyP1.BBTInterleaved
