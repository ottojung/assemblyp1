import AssemblyP1.P2RepeatResidual
import AssemblyP1.BBTSupportInvariant

/-!
# The triple analogue of `AssemblyP1.P2RepeatResidual.maximal_extension_of_repeated`

## What this module proves

`AssemblyP1.P2RepeatResidual.maximal_extension_of_repeated` bridges **two**
occurrences of the same `(L-1)`-mer to a `Genome.IsRepeat` (a *two-sided maximal*
repeat) of length `e` with `L - 1 ≤ e < G`, and it uses primitivity exactly to
keep the combined extension below a full turn.  The same bridge for **three**
pairwise distinct occurrences was missing, and it is what the multiplicity-`≥ 3`
reading of the `SelectedTriple` branch needs:

```lean
theorem triple_extension_of_repeated
    (hG : 0 < G) (hL : 2 ≤ L) (S : Fin G → α)
    (a b c : Fin G) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hvu : vtx hG L S a = vtx hG L S b) (hvw : vtx hG L S a = vtx hG L S c)
    (hprim : IsPrimitive hG S) :
    ∃ (e : ℕ) (a' b' c' : Fin G),
      L - 1 ≤ e ∧ e < G ∧ (mkGenome hG S).IsTripleRepeat e a' b' c'
```

Since the first conjunct of `Genome.IsTripleRepeat` is `1 ≤ e` and the second is
`e < S.len`, a `Genome.IsTripleRepeat` of length `e ≥ L - 1` is exactly a
violation of the **triple clause of `P2`** at read length `L`.  Hence:

```lean
theorem not_SelectedTriple_of_P2_primitive   -- `¬ SelectedTriple θ`
theorem mer_multiplicity_le_two_of_P2_primitive  -- θ-free form
```

That θ-free form is the "no `(L-1)`-mer of multiplicity `≥ 3` on a primitive
`P2` genome" lemma: a `(L-1)`-mer `v` with `3 ≤ (fibre hG L S v).card` has three
pairwise distinct starts of the truth spelling `v`, i.e. three distinct starts in
`fibre hG L S v`, and `fibre` is by definition the set of starts spelling `v`.

## Where primitivity is used, and only there

`IsPrimitive` here is `AssemblyP1.RepeatAdapter.IsPrimitive` (`no shift
`1 ≤ s < G` is a symmetry of the word`), the notion already used by
`P2RepeatResidual`, brought in by `open AssemblyP1.RepeatAdapter`.  It is used in
exactly the three places listed in the header of `P2RepeatResidual`, and in
exactly the same way:

* `not_mem_tripleLeft_G` / `not_mem_tripleRight_G`: the two-sided extension of
  the group cannot reach a full turn, because then the pair `a, b` would agree
  on `G` consecutive positions (`no_left_ext_of_G`, `no_right_ext_of_G`);
* `combined_below_G`: `ℓ + (L-1) + r < G`, because otherwise the *shifted* pair
  agrees on `≥ G` consecutive positions (`not_primitive_of_ge_G_agree`).

Group uniform extension is what makes the `Genome.IsTripleRepeat` maximality
clauses available.  `LeftAgree_not_succ` / `RightAgree_not_succ` are applied to
the pair `a, b` inside the triple group: at the maximal amounts the *pair* `a, b`
already has differing predecessor and differing follower symbols, which is
exactly `¬ (Preceding a' = Preceding b' ∧ Preceding b' = Preceding c')`.

## What this module does not prove

Nothing about `θ`, `Selects`, `Function.Bijective`, `FibrePreserving` or
`OneCycle`: the statement here is genome-intrinsic.  It says nothing about the
*interleaved* disjunct of `BBTEulerian.LongObstruction`, which is the live
residual of the #89 endgame (`BOARD94-ENDGAME-1000.md` §6 step 4).  It uses no
`sorry`, no `admit`, no `native_decide`, no `unsafe`, no new `axiom`, and no
weakened hypothesis: primitivity and `P2` are used as stated.
-/

set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace AssemblyP1.P2TripleResidual

open SourceFaithfulIs
open OrientedRigidity
open AssemblyP1.RepeatAdapter
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.P2RepeatResidual
open AssemblyP1
open AssemblyP1.BBTSupport

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-! ## 1. The two-sided extension of a *group* of three starts -/

/-- The `k` positions preceding all three of `A`, `B`, `C` agree (pairwise). -/
def TripleLeft (hG : 0 < G) (S : Fin G → α) (A B C k : ℕ) : Prop :=
  LeftAgree hG S A B k ∧ LeftAgree hG S A C k

/-- The `k` positions from `A + n`, `B + n`, `C + n` onwards agree (pairwise). -/
def TripleRight (hG : 0 < G) (S : Fin G → α) (A B C n k : ℕ) : Prop :=
  RightAgree hG S A B n k ∧ RightAgree hG S A C n k

instance (hG : 0 < G) (S : Fin G → α) (A B C k : ℕ) : Decidable (TripleLeft hG S A B C k) := by
  unfold TripleLeft; infer_instance

instance (hG : 0 < G) (S : Fin G → α) (A B C n k : ℕ) : Decidable (TripleRight hG S A B C n k) := by
  unfold TripleRight; infer_instance

theorem zero_mem_tripleLeft (hG : 0 < G) (S : Fin G → α) (A B C : ℕ) :
    TripleLeft hG S A B C 0 := ⟨by intro d hd; omega, by intro d hd; omega⟩

theorem zero_mem_tripleRight (hG : 0 < G) (S : Fin G → α) (A B C n : ℕ) :
    TripleRight hG S A B C n 0 := ⟨by intro d hd; omega, by intro d hd; omega⟩

/-- **A left extension of a full turn of the group contradicts primitivity**, on
the pair `A, B` alone. -/
theorem not_mem_tripleLeft_G {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B C : ℕ}
    (hAB : A % G ≠ B % G) (hprim : IsPrimitive hG S) : ¬ TripleLeft hG S A B C G := by
  intro h
  exact (no_left_ext_of_G hG S hAB h.1 hprim).elim

/-- Likewise for the right extension. -/
theorem not_mem_tripleRight_G {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B C n : ℕ}
    (hAB : (A + n) % G ≠ (B + n) % G) (hprim : IsPrimitive hG S) :
    ¬ TripleRight hG S A B C n G := by
  intro h
  exact (no_right_ext_of_G hG S hAB h.1 hprim).elim

/-- **Left agreement is transitive on the second position**, which is what lets
the pair `B, C` of a group inherit the group's maximal left extension. -/
theorem LeftAgree_trans {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B C k : ℕ}
    (h1 : LeftAgree hG S A B k) (h2 : LeftAgree hG S A C k) : LeftAgree hG S B C k := by
  intro d hd
  exact (h1 d hd).symm.trans (h2 d hd)

/-- **Right agreement is transitive on the second position.** -/
theorem RightAgree_trans {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B C n k : ℕ}
    (h1 : RightAgree hG S A B n k) (h2 : RightAgree hG S A C n k) :
    RightAgree hG S B C n k := by
  intro d hd
  exact (h1 d hd).symm.trans (h2 d hd)

/-- **Left agreement is symmetric.** -/
theorem LeftAgree_symm {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B k : ℕ}
    (h : LeftAgree hG S A B k) : LeftAgree hG S B A k := by
  intro d hd
  exact (h d hd).symm

/-- **Right agreement is symmetric.** -/
theorem RightAgree_symm {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B n k : ℕ}
    (h : RightAgree hG S A B n k) : RightAgree hG S B A n k := by
  intro d hd
  exact (h d hd).symm

/-- **A decidable predicate on `ℕ` that holds at `0` and fails at `hG` has a
largest `ℓ < hG` at which it holds.**  This is the only maximality extractor
the triple bridge needs, stated once over an arbitrary predicate so that it can
be applied to `TripleLeft` and to `TripleRight` alike. -/
theorem exists_max_lt_of_zero {P : ℕ → Prop} [DecidablePred P] {hG : ℕ}
    (h0 : P 0) (hnG : ¬ P hG) : ∃ ℓ : ℕ, ℓ < hG ∧ P ℓ ∧ ¬ P (ℓ + 1) := by
  have hpos : 0 < hG := by
    by_contra h
    exact hnG (by rw [show hG = 0 from by omega]; exact h0)
  let T : Finset ℕ := (Finset.range hG).filter P
  have hne : T.Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h0⟩⟩
  have hmax : T.max' hne ∈ T := Finset.max'_mem _ hne
  have hlt : T.max' hne < hG := Finset.mem_range.mp (Finset.mem_filter.mp hmax).1
  have hP : P (T.max' hne) := (Finset.mem_filter.mp hmax).2
  refine ⟨T.max' hne, hlt, hP, ?_⟩
  intro hc
  have hlt1 : T.max' hne + 1 < hG := by
    by_contra hc2
    have heq : T.max' hne + 1 = hG := by omega
    exact absurd (heq ▸ hc) hnG
  have hmem1 : T.max' hne + 1 ∈ T :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt1, hc⟩
  exact absurd (Finset.le_max' _ _ hmem1) (by omega)

/-- **The maximal left extension of the group**: an amount `ℓ < G` which is not
extendable by one symbol. -/
theorem exists_maxTripleLeft {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B C : ℕ}
    (hAB : A % G ≠ B % G) (hprim : IsPrimitive hG S) :
    ∃ ℓ : ℕ, ℓ < G ∧ TripleLeft hG S A B C ℓ ∧ ¬ TripleLeft hG S A B C (ℓ + 1) :=
  exists_max_lt_of_zero (zero_mem_tripleLeft hG S A B C)
    (not_mem_tripleLeft_G hG S hAB hprim)

/-- **The maximal right extension of the group**. -/
theorem exists_maxTripleRight {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B C n : ℕ}
    (hAB : (A + n) % G ≠ (B + n) % G) (hprim : IsPrimitive hG S) :
    ∃ r : ℕ, r < G ∧ TripleRight hG S A B C n r ∧ ¬ TripleRight hG S A B C n (r + 1) :=
  exists_max_lt_of_zero (zero_mem_tripleRight hG S A B C n)
    (not_mem_tripleRight_G hG S hAB hprim)

/-! ## 2. Arithmetic: the extended starts agree on the whole extended word -/

/-- `Preceding` and `Following` at a start read as `cyc` at the corresponding
integer position.  This is what lets the maximality clauses of
`Genome.IsTripleRepeat` be discharged as congruence statements, exactly as in
`P2RepeatResidual.maximal_extension_of_repeated`. -/
theorem Preceding_eq_cyc (hG : 0 < G) (S : Fin G → α) {A : ℕ} (hA : A < G) :
    (mkGenome hG S).Preceding ⟨A, hA⟩ = cyc hG S (A + G - 1) := rfl

theorem Following_eq_cyc (hG : 0 < G) (S : Fin G → α) (e : ℕ) {A : ℕ} (hA : A < G) :
    (mkGenome hG S).Following e ⟨A, hA⟩ = cyc hG S (A + e) := rfl

/-- **The two-sided extension of a *pair*, as pure index arithmetic.**  Given a
left agreement of `ℓ` symbols, a seed agreement of `n` symbols and a right
agreement of `r` symbols at the distinct residues `A`, `B`, the two starts
shifted left by `ℓ` agree on the whole `ℓ + n + r` window.  This is the
computation of `P2RepeatResidual.maximal_extension_of_repeated`, factored out so
that the triple case can apply it to each pair. -/
theorem pair_extended_agree {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B ℓ n r : ℕ}
    (hℓG : ℓ < G)
    (hLag : LeftAgree hG S A B ℓ)
    (hseed : ∀ d : ℕ, d < n → cyc hG S (A + d) = cyc hG S (B + d))
    (hRag : RightAgree hG S A B n r) :
    ∀ d : ℕ, d < ℓ + n + r →
      cyc hG S ((A + G - ℓ) % G + d) = cyc hG S ((B + G - ℓ) % G + d) := by
  intro d hd
  have hdA : ((A + G - ℓ) % G + d) % G = (A + G - ℓ + d) % G :=
    Nat.add_mod_eq_add_mod_right d (Nat.mod_mod (A + G - ℓ) G)
  have hdB : ((B + G - ℓ) % G + d) % G = (B + G - ℓ + d) % G :=
    Nat.add_mod_eq_add_mod_right d (Nat.mod_mod (B + G - ℓ) G)
  rw [cyc_congr' hG S hdA, cyc_congr' hG S hdB]
  by_cases hd1 : d < ℓ
  · -- inside the maximal left extension
    have hd' : ℓ - 1 - d < ℓ := by omega
    have h := hLag (ℓ - 1 - d) hd'
    calc cyc hG S (A + G - ℓ + d)
        = cyc hG S (A + G - 1 - (ℓ - 1 - d)) := by rw [show
            A + G - ℓ + d = A + G - 1 - (ℓ - 1 - d) from by omega]
      _ = cyc hG S (B + G - 1 - (ℓ - 1 - d)) := h
      _ = cyc hG S (B + G - ℓ + d) := by rw [show
          B + G - 1 - (ℓ - 1 - d) = B + G - ℓ + d from by omega]
  · by_cases hd2 : d < ℓ + n
    · -- inside the seed
      have hd' : d - ℓ < n := by omega
      calc cyc hG S (A + G - ℓ + d)
          = cyc hG S ((A + (d - ℓ)) + G) := by rw [show
              A + G - ℓ + d = (A + (d - ℓ)) + G from by omega]
        _ = cyc hG S (A + (d - ℓ)) := cyc_congr' hG S (add_G_mod' _)
        _ = cyc hG S (B + (d - ℓ)) := hseed _ hd'
        _ = cyc hG S (B + G - ℓ + d) := by rw [show
            B + G - ℓ + d = (B + (d - ℓ)) + G from by omega,
          ← cyc_congr' hG S (add_G_mod' _)]
    · -- inside the maximal right extension
      have hd' : d - (ℓ + n) < r := by omega
      calc cyc hG S (A + G - ℓ + d)
          = cyc hG S ((A + n + (d - (ℓ + n))) + G) := by rw [show
              A + G - ℓ + d = (A + n + (d - (ℓ + n))) + G from by omega]
        _ = cyc hG S (A + n + (d - (ℓ + n))) := cyc_congr' hG S (add_G_mod' _)
        _ = cyc hG S (B + n + (d - (ℓ + n))) := hRag _ hd'
        _ = cyc hG S (B + G - ℓ + d) := by rw [show
            B + G - ℓ + d = (B + n + (d - (ℓ + n))) + G from by omega,
          ← cyc_congr' hG S (add_G_mod' _)]

/-- Shifting two distinct residues by `ℓ` keeps them distinct. -/
theorem mod_shift_ne {G ℓ A B : ℕ} (hℓG : ℓ < G) (hAB : A % G ≠ B % G) :
    (A + G - ℓ) % G ≠ (B + G - ℓ) % G := by
  intro h
  have h1 : ((A + G - ℓ) % G + ℓ) % G = ((B + G - ℓ) % G + ℓ) % G :=
    congrArg (fun t : ℕ => (t + ℓ) % G) h
  have hA : ((A + G - ℓ) % G + ℓ) % G = A % G := by
    refine Eq.trans (Nat.add_mod_eq_add_mod_right ℓ (Nat.mod_mod (A + G - ℓ) G)) ?_
    have e1 : A + G - ℓ + ℓ = A + G :=
      Nat.sub_add_cancel (le_trans (Nat.le_of_lt hℓG) (Nat.le_add_left G A))
    rw [e1, add_G_mod']
  have hB : ((B + G - ℓ) % G + ℓ) % G = B % G := by
    refine Eq.trans (Nat.add_mod_eq_add_mod_right ℓ (Nat.mod_mod (B + G - ℓ) G)) ?_
    have e1 : B + G - ℓ + ℓ = B + G :=
      Nat.sub_add_cancel (le_trans (Nat.le_of_lt hℓG) (Nat.le_add_left G B))
    rw [e1, add_G_mod']
  exact hAB (hA.symm.trans (h1.trans hB))

/-! ## 3. The triple bridge -/

/-- **The maximality of a left extension, read as `Preceding`.**  If the copies
at `A', B' = (A + G - ℓ) % G, (B + G - ℓ) % G` agree on the `ℓ` preceding
positions but not on `ℓ + 1`, then their preceding symbols differ.  This is the
reading of `LeftAgree_not_succ` through `Genome.Preceding`. -/
theorem preceding_ne_of_leftMax {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B ℓ : ℕ}
    (hℓG : ℓ < G) (h : LeftAgree hG S A B ℓ) (hn : ¬ LeftAgree hG S A B (ℓ + 1)) :
    (mkGenome hG S).Preceding ⟨(A + G - ℓ) % G, Nat.mod_lt _ hG⟩ ≠
      (mkGenome hG S).Preceding ⟨(B + G - ℓ) % G, Nat.mod_lt _ hG⟩ := by
  have hneP : cyc hG S (A + G - 1 - ℓ) ≠ cyc hG S (B + G - 1 - ℓ) :=
    LeftAgree_not_succ h hn
  intro hP
  apply hneP
  have hcongr : cyc hG S ((A + G - ℓ) % G + G - 1) = cyc hG S (A + G - 1 - ℓ) := by
    refine cyc_congr' hG S ?_
    have h2 := Nat.add_mod_eq_add_mod_right (G - 1) (Nat.mod_mod (A + G - ℓ) G)
    rw [show (A + G - ℓ) % G + (G - 1) = (A + G - ℓ) % G + G - 1 from by omega,
      show A + G - ℓ + (G - 1) = (A + G - 1 - ℓ) + G from by omega,
      add_G_mod'] at h2
    exact h2
  have hcongr' : cyc hG S ((B + G - ℓ) % G + G - 1) = cyc hG S (B + G - 1 - ℓ) := by
    refine cyc_congr' hG S ?_
    have h2 := Nat.add_mod_eq_add_mod_right (G - 1) (Nat.mod_mod (B + G - ℓ) G)
    rw [show (B + G - ℓ) % G + (G - 1) = (B + G - ℓ) % G + G - 1 from by omega,
      show B + G - ℓ + (G - 1) = (B + G - 1 - ℓ) + G from by omega,
      add_G_mod'] at h2
    exact h2
  have hPA := Preceding_eq_cyc hG S (Nat.mod_lt (A + G - ℓ) hG)
  have hPB := Preceding_eq_cyc hG S (Nat.mod_lt (B + G - ℓ) hG)
  exact hcongr.symm.trans ((hPA.symm.trans (hP.trans hPB)).trans hcongr')

/-- **The maximality of a right extension, read as `Following`.**  If the copies
at the shifted starts agree on the `r` positions following the seed of length
`n` but not on `r + 1`, then their following symbols differ. -/
theorem following_ne_of_rightMax {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B ℓ n r : ℕ}
    (hℓG : ℓ < G) (h : RightAgree hG S A B n r) (hn : ¬ RightAgree hG S A B n (r + 1)) :
    (mkGenome hG S).Following (ℓ + n + r) ⟨(A + G - ℓ) % G, Nat.mod_lt _ hG⟩ ≠
      (mkGenome hG S).Following (ℓ + n + r) ⟨(B + G - ℓ) % G, Nat.mod_lt _ hG⟩ := by
  have hneF : cyc hG S (A + n + r) ≠ cyc hG S (B + n + r) := RightAgree_not_succ h hn
  intro hP
  apply hneF
  have hcongr : cyc hG S ((A + G - ℓ) % G + (ℓ + n + r)) = cyc hG S (A + n + r) := by
    refine cyc_congr' hG S ?_
    have h2 := Nat.add_mod_eq_add_mod_right (ℓ + n + r) (Nat.mod_mod (A + G - ℓ) G)
    rw [show A + G - ℓ + (ℓ + n + r) = (A + n + r) + G from by omega, add_G_mod'] at h2
    exact h2
  have hcongr' : cyc hG S ((B + G - ℓ) % G + (ℓ + n + r)) = cyc hG S (B + n + r) := by
    refine cyc_congr' hG S ?_
    have h2 := Nat.add_mod_eq_add_mod_right (ℓ + n + r) (Nat.mod_mod (B + G - ℓ) G)
    rw [show B + G - ℓ + (ℓ + n + r) = (B + n + r) + G from by omega, add_G_mod'] at h2
    exact h2
  have hFA := Following_eq_cyc hG S (ℓ + n + r) (Nat.mod_lt (A + G - ℓ) hG)
  have hFB := Following_eq_cyc hG S (ℓ + n + r) (Nat.mod_lt (B + G - ℓ) hG)
  exact hcongr.symm.trans ((hFA.symm.trans (hP.trans hFB)).trans hcongr')

/-! ## 4. The triple bridge proper -/

/-- **The triple maximal-extension bridge.**  Three pairwise distinct starts of a
primitive truth spelling the same `(L-1)`-mer lie inside a `Genome.IsTripleRepeat`
of length `e` with `L - 1 ≤ e < G`.

This is the triple analogue of `P2RepeatResidual.maximal_extension_of_repeated`,
and it uses primitivity in exactly the three places listed in §"Where primitivity
is used" above. -/
theorem triple_extension_of_repeated {G : ℕ} (hG : 0 < G) {L : ℕ} (hL : 2 ≤ L)
    (S : Fin G → α) (a b c : Fin G) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hvu : vtx hG L S a = vtx hG L S b) (hvw : vtx hG L S a = vtx hG L S c)
    (hprim : IsPrimitive hG S) :
    ∃ (e : ℕ) (a' b' c' : Fin G),
      L - 1 ≤ e ∧ e < G ∧ (mkGenome hG S).IsTripleRepeat e a' b' c' := by
  have hnpos : 1 ≤ L - 1 := by omega
  have hAB : a.val % G ≠ b.val % G := by
    intro h
    exact hab (Fin.ext ((Nat.mod_eq_of_lt a.isLt).symm.trans
      (h.trans (Nat.mod_eq_of_lt b.isLt))))
  have hAC : a.val % G ≠ c.val % G := by
    intro h
    exact hac (Fin.ext ((Nat.mod_eq_of_lt a.isLt).symm.trans
      (h.trans (Nat.mod_eq_of_lt c.isLt))))
  have hBC : b.val % G ≠ c.val % G := by
    intro h
    exact hbc (Fin.ext ((Nat.mod_eq_of_lt b.isLt).symm.trans
      (h.trans (Nat.mod_eq_of_lt c.isLt))))
  -- the seed: all three occurrences spell the same `(L-1)`-mer
  have hagAB : ∀ d : ℕ, d < L - 1 → cyc hG S (a.val + d) = cyc hG S (b.val + d) := by
    intro d hd
    have hv := congrFun hvu (⟨d, hd⟩ : Fin (L - 1))
    simpa only [vtx, nodeWindow, cyc] using hv
  have hagAC : ∀ d : ℕ, d < L - 1 → cyc hG S (a.val + d) = cyc hG S (c.val + d) := by
    intro d hd
    have hv := congrFun hvw (⟨d, hd⟩ : Fin (L - 1))
    simpa only [vtx, nodeWindow, cyc] using hv
  have hagBC : ∀ d : ℕ, d < L - 1 → cyc hG S (b.val + d) = cyc hG S (c.val + d) := by
    intro d hd
    have hv := congrFun (hvu.symm.trans hvw) (⟨d, hd⟩ : Fin (L - 1))
    simpa only [vtx, nodeWindow, cyc] using hv
  -- the two maximal extensions of the *group*
  obtain ⟨ℓ, hℓG, hLagAnd, hLag'⟩ :=
    exists_maxTripleLeft (A := a.val) (B := b.val) (C := c.val) hG S hAB hprim
  obtain ⟨hLagB, hLagC⟩ := hLagAnd
  obtain ⟨r, hrG, hRagAnd, hRag'⟩ :=
    exists_maxTripleRight (A := a.val) (B := b.val) (C := c.val) (n := L - 1) hG S
      (by intro hcon; exact hAB (mod_add_cancel_right hcon)) hprim
  obtain ⟨hRagB, hRagC⟩ := hRagAnd
  -- the pair `b, c` inherits the group's extensions: agreement is transitive
  have hLagBC : LeftAgree hG S b.val c.val ℓ :=
    fun d hd => (hLagB d hd).symm.trans (hLagC d hd)
  have hRagBC : RightAgree hG S b.val c.val (L - 1) r :=
    fun d hd => (hRagB d hd).symm.trans (hRagC d hd)
  -- the shifted starts, as integers below `G`
  have hA'lt : (a.val + G - ℓ) % G < G := Nat.mod_lt _ hG
  have hB'lt : (b.val + G - ℓ) % G < G := Nat.mod_lt _ hG
  have hC'lt : (c.val + G - ℓ) % G < G := Nat.mod_lt _ hG
  have hA'B'mod : (a.val + G - ℓ) % G ≠ (b.val + G - ℓ) % G := mod_shift_ne hℓG hAB
  have hA'C'mod : (a.val + G - ℓ) % G ≠ (c.val + G - ℓ) % G := mod_shift_ne hℓG hAC
  have hB'C'mod : (b.val + G - ℓ) % G ≠ (c.val + G - ℓ) % G := mod_shift_ne hℓG hBC
  -- the pairwise agreement of the shifted starts on the whole extended word
  have hagAB' := pair_extended_agree hG S hℓG hLagB hagAB hRagB
  have hagAC' := pair_extended_agree hG S hℓG hLagC hagAC hRagC
  have hagBC' := pair_extended_agree hG S hℓG hLagBC hagBC hRagBC
  -- **primitivity bounds the combined extension**, again on the pair `a, b`
  have heG : ℓ + (L - 1) + r < G := by
    by_contra hcon
    have heG' : G ≤ ℓ + (L - 1) + r := by omega
    exact not_primitive_of_ge_G_agree hG S ((a.val + G - ℓ) % G) ((b.val + G - ℓ) % G)
      (ℓ + (L - 1) + r) (by simpa only [Nat.mod_mod] using hA'B'mod) heG' hagAB' hprim
  have hA'B'Fin : (⟨(a.val + G - ℓ) % G, hA'lt⟩ : Fin G) ≠ ⟨(b.val + G - ℓ) % G, hB'lt⟩ := by
    intro h
    exact hA'B'mod (congrArg Fin.val h)
  have hA'C'Fin : (⟨(a.val + G - ℓ) % G, hA'lt⟩ : Fin G) ≠ ⟨(c.val + G - ℓ) % G, hC'lt⟩ := by
    intro h
    exact hA'C'mod (congrArg Fin.val h)
  have hB'C'Fin : (⟨(b.val + G - ℓ) % G, hB'lt⟩ : Fin G) ≠ ⟨(c.val + G - ℓ) % G, hC'lt⟩ := by
    intro h
    exact hB'C'mod (congrArg Fin.val h)
  refine ⟨ℓ + (L - 1) + r, ⟨(a.val + G - ℓ) % G, hA'lt⟩, ⟨(b.val + G - ℓ) % G, hB'lt⟩,
    ⟨(c.val + G - ℓ) % G, hC'lt⟩, by omega, heG, ?_⟩
  refine ⟨(by omega : 1 ≤ ℓ + (L - 1) + r), heG, hA'B'Fin, hA'C'Fin, hB'C'Fin,
    fun d => hagAB' d.val d.isLt, fun d => hagAC' d.val d.isLt,
    fun d => hagBC' d.val d.isLt, ?_, ?_⟩
  · -- the three preceding symbols are not all equal: whichever pair the group's
    -- left maximality blocks already forces a change of preceding symbol
    by_cases hAB1 : LeftAgree hG S a.val b.val (ℓ + 1)
    · -- the pair `a, c` is blocked: `Preceding a' ≠ Preceding c'`
      have hneP := preceding_ne_of_leftMax hG S hℓG hLagC
        (fun h => hLag' ⟨hAB1, h⟩)
      intro hand
      exact hneP (hand.1.trans hand.2)
    · -- the pair `a, b` is blocked: `Preceding a' ≠ Preceding b'`
      have hneP := preceding_ne_of_leftMax hG S hℓG hLagB hAB1
      intro hand
      exact hneP hand.1
  · -- the three following symbols are not all equal: same case split on the right
    by_cases hAB1 : RightAgree hG S a.val b.val (L - 1) (r + 1)
    · have hneF := following_ne_of_rightMax hG S hℓG hRagC
        (fun h => hRag' ⟨hAB1, h⟩)
      intro hand
      exact hneF (hand.1.trans hand.2)
    · have hneF := following_ne_of_rightMax hG S hℓG hRagB hAB1
      intro hand
      exact hneF hand.1

/-! ## 4. The primitivity lemma: no `(L-1)`-mer of multiplicity `≥ 3` -/

/-- **The primitivity lemma, θ-free form.**  On a primitive `P2` genome, no
`(L-1)`-mer occurs three or more times: every vertex of the condensed
`(L-1)`-mer multigraph has out-degree `≤ 2`.

`fibre hG L S v` is by definition the set of starts spelling `v`
(`BBTCondense.mem_fibre`), so `3 ≤ (fibre hG L S v).card` is literally "the
`(L-1)`-mer `v` has multiplicity `≥ 3"`. -/
theorem mer_multiplicity_le_two_of_P2_primitive {G : ℕ} (hG : 0 < G) {L : ℕ} (hL : 2 ≤ L)
    (S : Fin G → α) (hP2 : P2 hG L S) (hprim : IsPrimitive hG S) :
    ∀ v : Fin (L - 1) → α, (fibre hG L S v).card ≤ 2 := by
  intro v
  by_contra hcard
  have htwo : 2 < (fibre hG L S v).card := by omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp htwo
  have hva : vtx hG L S a = v := (mem_fibre hG L S (v := v) (r := a)).mp ha
  have hvb : vtx hG L S b = v := (mem_fibre hG L S (v := v) (r := b)).mp hb
  have hvc : vtx hG L S c = v := (mem_fibre hG L S (v := v) (r := c)).mp hc
  obtain ⟨e, a', b', c', he, heG, htri⟩ :=
    triple_extension_of_repeated hG hL S a b c hab hac hbc
      (hva.trans hvb.symm) (hva.trans hvc.symm) hprim
  have hlt : e < L - 1 := hP2.1 ⟨e, heG⟩ a' b' c' htri
  omega

/-- **The primitivity lemma in the form the endgame consumes: `¬ SelectedTriple`
on a primitive `P2` genome, at every successor map `θ`.**

`SelectedTriple θ` is `∃ v, 3 ≤ (fibre v).card ∧ Selects θ v`
(`BBTSupport.SelectedTriple`), so it is exactly the multiplicity-`≥ 3` clause;
the primitivity lemma above refutes the first conjunct of that existential, so
the `Selects` conjunct is never needed and no hypothesis on `θ` is used. -/
theorem not_SelectedTriple_of_P2_primitive {G : ℕ} (hG : 0 < G) {L : ℕ} (hL : 2 ≤ L)
    (S : Fin G → α) (hP2 : P2 hG L S) (hprim : IsPrimitive hG S)
    (θ : Fin G → Fin G) :
    ¬ SelectedTriple (hG := hG) (L := L) S θ := by
  rintro ⟨v, hcard, hsel⟩
  have hle := mer_multiplicity_le_two_of_P2_primitive hG hL S hP2 hprim v
  omega

/-- The θ-free statement, phrased as the absence of a long triple repeat, which
is the shape `P2`'s own triple clause denies: a `P2` genome of length-`L` reads
has **no** `Genome.IsTripleRepeat` of length `≥ L - 1`, primitive or not.  The
content of `not_SelectedTriple_of_P2_primitive` above is exactly the step that
turns a multiplicity-`≥ 3` `(L-1)`-mer into such a triple repeat. -/
theorem no_long_triple_repeat_of_P2 {G : ℕ} (hG : 0 < G) {L : ℕ} (_hL : 2 ≤ L)
    (S : Fin G → α) (hP2 : P2 hG L S) :
    ∀ e a b c : Fin G, (mkGenome hG S).IsTripleRepeat e a b c → e.val < L - 1 :=
  fun e a b c h => hP2.1 e a b c h

end AssemblyP1.P2TripleResidual