import AssemblyP1.BBTUniqueEulerian
import AssemblyP1.P2Multiplicity
import AssemblyP1.RepeatAdapter

/-!
# `thm:BBT` Lemma 1: the degree fact, and the exact condition it needs (#94)

Front `94-tw6`.  This module is about the **degree fact** that Bresler--Bresler--Tse
use in the appendix proof of their Theorem 3, quoted by front `94-tw5` from
`appendix_short.tex` lines 157-175 (re-fetched, md5-identical):

> Note that the cycle `C_0` does not traverse any node three times in `G_0`,
> for this would imply the existence of a triple repeat of length `K`,
> violating the hypothesis of the Lemma.

The exact statement below is the one this module proves and characterises,
**in this repository's own vocabulary** (`BBTUniqueEulerian.vtx`,
`BBTUniqueEulerian.Agr3`, `BBTUniqueEulerian.Period`,
`BBTUniqueEulerian.leastPeriod`, `SourceFaithfulIs.Genome.IsTripleRepeat`,
`BBTSequenceGraph.deg`).

## 0. What is proved, in one paragraph

The **unrestricted** form of the source's degree fact — *any vertex of
out-degree at least three forces a maximal triple repeat of length `≥ K`* — is
**FALSE**, and §7 is a kernel-checked counterexample at `S = 012012012`,
`G = 9`, `K = 3`: the node `012` is spelled by the three distinct starts
`0, 3, 6` (so it is traversed three times) and **at those three starts, at
each of the lengths `e = 3`, `4` and `8`, there is no maximal triple repeat**
(`no_tripleRepeat_012012012`, `no_tripleRepeat4_012012012`,
`no_tripleRepeat8_012012012`).  What is true, and proved here, is the sharp
dichotomy
`deg_fact`: for `3 ≤ G` and `1 ≤ K < G`, either

* there is a `SourceFaithfulIs.Genome.IsTripleRepeat` of length `≥ K` (the
  `Ukkonen` triple clause is violated, which is BBT's contradiction), **or**
* the circular word has a genuine period `p` with `0 < p ≤ G`
  (`escape_iff_leastPeriod` : this happens exactly when
  `leastPeriod hG S < G`, i.e. exactly when `S` is an exact nontrivial power,
  equivalently `¬ RepeatAdapter.IsPrimitive hG S`).

So the degree fact **does** hold, in the source's own form, under precisely the
condition `deg_fact_of_primitive`: `∀ d, 0 < d → d < G → ¬ Period hG S d`
(primitivity).  This is the `p = 3` alternative that `BBTUniqueEulerian`'s
docstring names as "exactly the alternative in Lemma 1", now with a proof, a
decision procedure (`span` is a `Finset ℕ`, so `spanMax` is computable) and a
`by decide` counterexample.

## 1. Contents

* §0 — the bridges between the two word layers of this repository
  (`Agr3` vs. `Genome.Agree`, `Preceding`, `Following`).
* §1 — `span`, the `Finset` of agreement lengths realised by **some** triple of
  distinct starts; `spanMax`; the decision procedure.
* §2 — `max_span_tripleRepeat`: the maximum of `span`, if it is `< G`, is a
  `Genome.IsTripleRepeat`.  This is the whole content of the two-sided
  maximality: it is *not* obtainable one maximality clause at a time.
* §3 — `max_span_escape`: if the maximum is `G`, there is a genuine period, and
  the three starts are pairwise congruent modulo the least period.
* §4 — `deg_fact`, the dichotomy; `deg_fact_of_primitive`, the source's exact
  statement; `no_three_of_primitive` and `deg_fact_node`, the same thing in the
  out-degree (number of traversals) reading.
* §5 — the `Ukkonen` / `P2` corollaries in `BBTUniqueEulerian` vocabulary:
  `no_three_of_Ukkonen`, `no_three_of_P2`, `prim_deg_le_two`.
* §6 — `escape_iff_leastPeriod`, `escape_iff_not_IsPrimitive`: the condition
  under which the degree fact holds, characterised three ways.
* §7 — the kernel-checked refutation of the unrestricted form, at
  `S = 012012012`, `G = 9`, `K = 3`.

No `sorry`, no `admit`, no new axiom, no changed definition.  Nothing in
`BBTUniqueEulerian`, `BBTEulerian`, `BBTLadder`, `PopulationUniqueness` or
`BBTTripleBridge` is modified.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AssemblyP1.Issue94TW6Lemma1

open SourceFaithfulIs
open OrientedRigidity
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.P2

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-! ## 0. The two word layers agree

This repository carries the word twice: `BBTUniqueEulerian` works with
`cyc`-indexed `Fin G` starts and `BBTUniqueEulerian.Agr3`, and the *source*
predicates (`P2`, `Ukkonen`) are `SourceFaithfulIs.Genome` predicates on
`P2.mkGenome hG S`.  The next three lemmas say the two are the same statements,
so that a theorem proved in the `Agr3` language *is* a theorem about
`IsTripleRepeat`. -/

/-- Three-fold agreement in `BBTUniqueEulerian` language is pairwise
`Genome.Agree` at the same length. -/
theorem agr3_iff_agree3 {a b c : Fin G} (e : ℕ) :
    Agr3 hG S a b c e ↔
      ((mkGenome hG S).Agree e a b ∧ (mkGenome hG S).Agree e a c) := by
  constructor
  · intro h
    exact ⟨fun d => (h d).1, fun d => (h d).2⟩
  · rintro ⟨h1, h2⟩ d
    exact ⟨h1 d, h2 d⟩

/-- `Preceding` in the source layer is the symbol one step back on the circle. -/
theorem preceding_eq (a : Fin G) :
    (mkGenome hG S).Preceding a = cyc hG S (a.val + G - 1) := rfl

/-- `Following` in the source layer is the symbol one step past the copy. -/
theorem following_eq (a : Fin G) (e : ℕ) :
    (mkGenome hG S).Following e a = cyc hG S (a.val + e) := rfl

/-- A whole turn of the circle changes nothing. -/
private theorem cyc_add_G' (x : ℕ) : cyc hG S (x + G) = cyc hG S x := by
  unfold cyc
  congr 1
  apply Fin.ext
  simp

/-! ## 1. The agreement lengths realised by three distinct starts

`span` is the set of lengths `e ≤ G` for which **some** three pairwise distinct
starts have equal length-`e` windows.  It is a `Finset ℕ`, so its maximum is
computable; §2 and §3 say exactly what that maximum means.  Note the
existential over the starts: the maximal triple need not be the original
`(a, b, c)`, which is precisely why `BBTTripleBridge`'s two-sided extension
engine is needed in *its* formulation and is not needed here. -/

/-- The lengths `≤ G` realised by some triple of pairwise distinct starts. -/
noncomputable def span (hG : 0 < G) (S : Fin G → α) : Finset ℕ := by
  classical
  exact (Finset.range (G + 1)).filter
    (fun e => ∃ a b c : Fin G, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Agr3 hG S a b c e)

/-- Agreement at length `e ≤ G` by three pairwise distinct starts puts `e` in
`span`. -/
theorem mem_span {a b c : Fin G} {e : ℕ} (heG : e ≤ G)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hag : Agr3 hG S a b c e) :
    e ∈ span hG S := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
  exact ⟨a, b, c, hab, hac, hbc, hag⟩

/-- Membership in `span` delivers three distinct agreeing starts. -/
theorem span_mem {e : ℕ} (he : e ∈ span hG S) :
    ∃ a b c : Fin G, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Agr3 hG S a b c e := by
  exact (Finset.mem_filter.mp he).2

/-- Members of `span` are bounded by `G`. -/
theorem mem_span_range {e : ℕ} (he : e ∈ span hG S) : e ≤ G := by
  have h1 := Finset.mem_range.mp (Finset.mem_filter.mp he).1
  omega

/-- Three pairwise distinct points on a circle of at least three points. -/
private theorem three_distinct_of (hg : 0 < G) (hh : 3 ≤ G) :
    ∃ a b c : Fin G, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨⟨0, hg⟩, ⟨1, lt_of_lt_of_le (by norm_num) hh⟩,
    ⟨2, lt_of_lt_of_le (by norm_num) hh⟩, ?_, ?_, ?_⟩
  · exact fun h => absurd (congrArg Fin.val h) (by norm_num)
  · exact fun h => absurd (congrArg Fin.val h) (by norm_num)
  · exact fun h => absurd (congrArg Fin.val h) (by norm_num)

/-- Agreement at length `0` is vacuous, so any three distinct starts put `0` in
`span`.

**This theorem is dead code in the library, and `3 ≤ G` is not what makes the
rest of the module go through** (review finding 3): `deg_fact` and all its
descendants get nonemptiness of `span` from `span_nonempty`, which needs
`hex`, not `mem_span_zero`.  `h3` is genuinely redundant here, since three
pairwise distinct elements of `Fin G` already force `3 ≤ G`. -/
theorem mem_span_zero (h3 : 3 ≤ G) : 0 ∈ span hG S := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := three_distinct_of hG h3
  exact mem_span hG S (by omega) hab hac hbc (fun d => Fin.elim0 d)

/-- **The decision procedure.**  If some three distinct starts agree at length
`K ≤ G`, then `span` is nonempty and its maximum is the relevant object. -/
theorem span_nonempty {K : ℕ} (hKG : K ≤ G)
    (hex : ∃ a b c : Fin G, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Agr3 hG S a b c K) :
    (span hG S).Nonempty := by
  obtain ⟨a, b, c, h1, h2, h3, h4⟩ := hex
  exact ⟨K, mem_span hG S hKG h1 h2 h3 h4⟩

/-- The maximum agreement length realised by three distinct starts. -/
noncomputable def spanMax (hG : 0 < G) (S : Fin G → α)
    (h : (span hG S).Nonempty) : ℕ := (span hG S).max' h

theorem mem_spanMax (h : (span hG S).Nonempty) : spanMax hG S h ∈ span hG S :=
  Finset.max'_mem _ _

theorem le_spanMax (h : (span hG S).Nonempty) {e : ℕ} (he : e ∈ span hG S) :
    e ≤ spanMax hG S h :=
  Finset.le_max' _ _ he

/-- The maximum is at most `G`. -/
theorem spanMax_le (h : (span hG S).Nonempty) : spanMax hG S h ≤ G :=
  mem_span_range hG S (mem_spanMax hG S h)

/-! ## 1.1 Agreement over a whole turn, and the back-shift

The one technical point of §2 is that the *preceding* maximality clause has to
be obtained by shifting all three starts back by one, which is why the maximum
is taken over all triples and not over a fixed one. -/

/-- Three `ℕ`-starts whose length-`e` windows coincide.  Used only so that a
common back-shift needs no side conditions. -/
def TriAgreeAt (x y z e : ℕ) : Prop :=
  ∀ d : ℕ, d < e → cyc hG S (x + d) = cyc hG S (y + d) ∧
    cyc hG S (x + d) = cyc hG S (z + d)

theorem agr3_iff_triAgreeAt {a b c : Fin G} (e : ℕ) :
    Agr3 hG S a b c e ↔ TriAgreeAt hG S a.val b.val c.val e :=
  agr3_iff_forall_lt hG S a b c e

/-- `ℕ`-level agreement descends to residues, provided the length fits. -/
theorem agr3_of_triAgreeAt {x y z e : ℕ} (heG : e ≤ G)
    (h : TriAgreeAt hG S x y z e) :
    Agr3 hG S ⟨x % G, Nat.mod_lt _ hG⟩ ⟨y % G, Nat.mod_lt _ hG⟩
      ⟨z % G, Nat.mod_lt _ hG⟩ e := by
  intro d
  have h1 := h d.val d.isLt
  refine ⟨?_, ?_⟩
  · calc cyc hG S ((x % G) + d.val) = cyc hG S (x + d.val) := (cyc_add hG S x d.val).symm
    _ = cyc hG S (y + d.val) := h1.1
    _ = cyc hG S ((y % G) + d.val) := (cyc_add hG S y d.val)
  · calc cyc hG S ((x % G) + d.val) = cyc hG S (x + d.val) := (cyc_add hG S x d.val).symm
    _ = cyc hG S (z + d.val) := h1.2
    _ = cyc hG S ((z % G) + d.val) := (cyc_add hG S z d.val)

/-- Agreement over a full turn makes every `sh` between the three starts a
period.  The third one is obtained from the first two by transitivity inside
each window. -/
theorem period_of_agr3 {a b c : Fin G} (hag : Agr3 hG S a b c G) :
    Period hG S (sh hG a b) ∧ Period hG S (sh hG a c) ∧ Period hG S (sh hG b c) := by
  have hAB : ∀ d : Fin G, cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val) := by
    intro d
    exact ((agr3_iff_forall_lt hG S a b c G).mp hag d.val d.isLt).1
  have hAC : ∀ d : Fin G, cyc hG S (a.val + d.val) = cyc hG S (c.val + d.val) := by
    intro d
    exact ((agr3_iff_forall_lt hG S a b c G).mp hag d.val d.isLt).2
  have hBC : ∀ d : Fin G, cyc hG S (b.val + d.val) = cyc hG S (c.val + d.val) := by
    intro d
    exact (hAB d).symm.trans (hAC d)
  exact ⟨period_of_agree_all hG S hAB, period_of_agree_all hG S hAC,
    period_of_agree_all hG S hBC⟩

/-- **The shift identity used by the back-extension**: one step back along the
circle is a whole turn minus one, so the symbol at offset `d` of the
back-shifted window is the symbol at offset `d - 1` of the original window. -/
private theorem cyc_back (x d : ℕ) (hd : 0 < d) :
    cyc hG S (x + G - 1 + d) = cyc hG S (x + (d - 1)) := by
  have h1 : x + G - 1 + d = x + G + (d - 1) := by omega
  rw [h1]
  have h2 : x + G + (d - 1) = (x + (d - 1)) + G := by omega
  rw [h2, cyc_add_G']

/-- **Rotating the circle by a bounded shift is injective.** -/
private theorem rotAdd_injective (d : ℕ) (hd : d ≤ G) :
    Function.Injective (rotAdd hG d) := by
  intro x y hxy
  have hkey : G - d + d = G := Nat.sub_add_cancel hd
  calc x = rotAdd hG G x := (rotAdd_full hG x).symm
    _ = rotAdd hG (G - d + d) x := by rw [hkey]
    _ = rotAdd hG (G - d) (rotAdd hG d x) := (rotAdd_add hG (G - d) d x).symm
    _ = rotAdd hG (G - d) (rotAdd hG d y) := by rw [hxy]
    _ = rotAdd hG (G - d + d) y := rotAdd_add hG (G - d) d y
    _ = rotAdd hG G y := by rw [hkey]
    _ = y := rotAdd_full hG y

/-! ## 2. The maximum of `span`, if it is below `G`, is a maximal triple repeat -/

/-- **The core lemma.**  Let `e* = spanMax` and suppose `1 ≤ e* < G`.  Then some
three distinct starts carry a `Genome.IsTripleRepeat` of length exactly `e*`.

Both maximality clauses come from maximality of `e*`, but they come from
*different triples of starts*: the "following" clause from `(a, b, c)` itself,
the "preceding" clause from the triple shifted one step back.  This is why the
maximum is taken over all triples, and it is the point
`docs/bbt-unique-eulerian-89.md` §4 makes about the two clauses not being
obtainable one after the other. -/
theorem max_span_tripleRepeat {h : (span hG S).Nonempty} (he1 : 1 ≤ spanMax hG S h)
    (heG : spanMax hG S h < G) :
    ∃ a b c : Fin G, ∃ e : Fin G,
      (mkGenome hG S).IsTripleRepeat e a b c ∧ e.val = spanMax hG S h := by
  obtain ⟨a, b, c, hab, hac, hbc, hag⟩ := span_mem hG S (mem_spanMax hG S h)
  -- maximality of `e*` in `span`
  have hmax : ∀ x y z : Fin G, x ≠ y → x ≠ z → y ≠ z → ∀ e : ℕ, e ≤ G →
      Agr3 hG S x y z e → e ≤ spanMax hG S h :=
    fun x y z hxy hxz hyz e heG hag => le_spanMax hG S h (mem_span hG S heG hxy hxz hyz hag)
  -- agreement one step longer, at any triple of distinct starts, is impossible
  have hlong : ∀ x y z : Fin G, x ≠ y → x ≠ z → y ≠ z →
      Agr3 hG S x y z (spanMax hG S h + 1) → False :=
    fun x y z hxy hxz hyz hag' =>
      absurd (hmax x y z hxy hxz hyz (spanMax hG S h + 1) (by omega) hag') (by omega)
  -- the "following" flank differs, else `hlong`
  have hfol : ¬((mkGenome hG S).Following (spanMax hG S h) a =
        (mkGenome hG S).Following (spanMax hG S h) b ∧
      (mkGenome hG S).Following (spanMax hG S h) b =
        (mkGenome hG S).Following (spanMax hG S h) c) := by
    intro hcon
    apply hlong a b c hab hac hbc
    rw [agr3_iff_triAgreeAt (a := a) (b := b) (c := c)]
    intro d hd
    have hdG : d ≤ spanMax hG S h := by omega
    rcases Nat.eq_or_lt_of_le hdG with hdeq | hd'
    · -- `d = e*`: this is exactly the hypothesis
      subst hdeq
      rw [following_eq hG S a _, following_eq hG S b _, following_eq hG S c _] at hcon
      exact ⟨hcon.1, hcon.1.trans hcon.2⟩
    · exact ⟨(hag ⟨d, hd'⟩).1, (hag ⟨d, hd'⟩).2⟩
  refine ⟨a, b, c, ⟨spanMax hG S h, heG⟩, ?_, rfl⟩
  refine ⟨he1, heG, hab, hac, hbc, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((agr3_iff_agree3 hG S (a := a) (b := b) (c := c) (spanMax hG S h)).mp hag).1
  · exact ((agr3_iff_agree3 hG S (a := a) (b := b) (c := c) (spanMax hG S h)).mp hag).2
  · intro d
    exact (hag d).1.symm.trans (hag d).2
  · rintro ⟨h1, h2⟩
    -- the "preceding" flank: shift all three starts one step back
    have hpre : TriAgreeAt hG S (a.val + G - 1) (b.val + G - 1) (c.val + G - 1)
        (spanMax hG S h + 1) := by
      intro d hd
      rcases Nat.eq_zero_or_pos d with h0 | hpos
      · -- `d = 0`: the symbol immediately before each copy
        subst h0
        refine ⟨?_, ?_⟩
        · show cyc hG S (a.val + G - 1) = cyc hG S (b.val + G - 1)
          exact (preceding_eq hG S a).symm.trans (h1.trans (preceding_eq hG S b))
        · show cyc hG S (a.val + G - 1) = cyc hG S (c.val + G - 1)
          exact (preceding_eq hG S a).symm.trans (h1.trans (h2.trans (preceding_eq hG S c)))
      · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
        have h2t : t < spanMax hG S h := by omega
        have hh := hag ⟨t, h2t⟩
        refine ⟨?_, ?_⟩
        · calc cyc hG S (a.val + G - 1 + (t + 1)) = cyc hG S (a.val + t) :=
              (cyc_back hG S a.val (t + 1) hpos).trans
                (congrArg (fun n => cyc hG S (a.val + n)) (Nat.succ_sub_one t))
            _ = cyc hG S (b.val + t) := hh.1
            _ = cyc hG S (b.val + G - 1 + (t + 1)) :=
              (congrArg (fun n => cyc hG S (b.val + n)) (Nat.succ_sub_one t)).symm.trans
                (cyc_back hG S b.val (t + 1) hpos).symm
        · calc cyc hG S (a.val + G - 1 + (t + 1)) = cyc hG S (a.val + t) :=
              (cyc_back hG S a.val (t + 1) hpos).trans
                (congrArg (fun n => cyc hG S (a.val + n)) (Nat.succ_sub_one t))
            _ = cyc hG S (c.val + t) := hh.2
            _ = cyc hG S (c.val + G - 1 + (t + 1)) :=
              (congrArg (fun n => cyc hG S (c.val + n)) (Nat.succ_sub_one t)).symm.trans
                (cyc_back hG S c.val (t + 1) hpos).symm
    set A : Fin G := ⟨(a.val + G - 1) % G, Nat.mod_lt _ hG⟩ with hA
    set B : Fin G := ⟨(b.val + G - 1) % G, Nat.mod_lt _ hG⟩ with hB
    set C : Fin G := ⟨(c.val + G - 1) % G, Nat.mod_lt _ hG⟩ with hC
    have hAeq : A = rotAdd hG (G - 1) a := by
      apply Fin.ext
      show (a.val + G - 1) % G = (a.val + (G - 1)) % G
      have h1 : a.val + G - 1 = a.val + (G - 1) := by omega
      rw [h1]
    have hBeq : B = rotAdd hG (G - 1) b := by
      apply Fin.ext
      show (b.val + G - 1) % G = (b.val + (G - 1)) % G
      have h1 : b.val + G - 1 = b.val + (G - 1) := by omega
      rw [h1]
    have hCeq : C = rotAdd hG (G - 1) c := by
      apply Fin.ext
      show (c.val + G - 1) % G = (c.val + (G - 1)) % G
      have h1 : c.val + G - 1 = c.val + (G - 1) := by omega
      rw [h1]
    have hinj : Function.Injective (rotAdd hG (G - 1)) :=
      rotAdd_injective hG (G - 1) (by omega)
    have hAB : A ≠ B := by
      intro hh
      apply hab
      exact hinj (hAeq.symm.trans (hh.trans hBeq))
    have hAC : A ≠ C := by
      intro hh
      apply hac
      exact hinj (hAeq.symm.trans (hh.trans hCeq))
    have hBC : B ≠ C := by
      intro hh
      apply hbc
      exact hinj (hBeq.symm.trans (hh.trans hCeq))
    have h1G : spanMax hG S h + 1 ≤ G := by omega
    exact hlong A B C hAB hAC hBC (agr3_of_triAgreeAt hG S h1G hpre)
  · exact hfol

/-! ## 3. The escape: if the maximum is `G`, there is a genuine period -/

/-- If the maximum of `span` is `G`, the three witnessing starts agree over a
whole turn, so each pair is explained by the least period, which is itself a
genuine period. -/
theorem max_span_escape {h : (span hG S).Nonempty} (heG : G ≤ spanMax hG S h) :
    ∃ p : ℕ, 0 < p ∧ p < G ∧ Period hG S p := by
  obtain ⟨a, b, c, hab, hac, hbc, hag⟩ := span_mem hG S (mem_spanMax hG S h)
  have hSG := spanMax_le hG S h
  have hG_eq : spanMax hG S h = G := by omega
  have hAG : Agr3 hG S a b c G := by rw [hG_eq] at hag; exact hag
  obtain ⟨h1, h2, _⟩ := period_of_agr3 hG S hAG
  have hpos : 0 < sh hG a b := by
    by_contra hn
    apply hab
    have h1 : rotAdd hG 0 a = a := rotAdd_zero hG a
    have h2 : rotAdd hG (sh hG a b) a = b := rotAdd_sh hG a b
    have hn0 : sh hG a b = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp hn)
    rw [hn0] at h2
    exact h1.symm.trans h2
  refine ⟨sh hG a b, hpos, sh_lt hG a b, h1⟩

/-- In the escape case the three starts are pairwise congruent modulo the least
period (`sh_dvd_trans`). -/
theorem max_span_escape_congruent {h : (span hG S).Nonempty}
    (heG : G ≤ spanMax hG S h) :
    ∃ a b c : Fin G, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      leastPeriod hG S ∣ sh hG a b ∧ leastPeriod hG S ∣ sh hG a c ∧
      leastPeriod hG S ∣ sh hG b c := by
  obtain ⟨a, b, c, hab, hac, hbc, hag⟩ := span_mem hG S (mem_spanMax hG S h)
  have hSG := spanMax_le hG S h
  have hG_eq : spanMax hG S h = G := by omega
  have hAG : Agr3 hG S a b c G := by rw [hG_eq] at hag; exact hag
  obtain ⟨h1, h2, h3⟩ := period_of_agr3 hG S hAG
  have hspec := leastPeriod_spec hG S
  have hpG : leastPeriod hG S ∣ G := leastPeriod_dvd_G hG S
  have hdAB : leastPeriod hG S ∣ sh hG a b :=
    leastPeriod_dvd_period hG S (le_of_lt (sh_lt hG a b)) h1
  have hdAC : leastPeriod hG S ∣ sh hG a c :=
    leastPeriod_dvd_period hG S (le_of_lt (sh_lt hG a c)) h2
  have hdBC : leastPeriod hG S ∣ sh hG b c :=
    leastPeriod_dvd_period hG S (le_of_lt (sh_lt hG b c)) h3
  have hdAC' : leastPeriod hG S ∣ sh hG a c := sh_dvd_trans hG hpG hdAB hdBC
  exact ⟨a, b, c, hab, hac, hbc, hdAB, hdAC', hdBC⟩

/-! ## 4. The degree fact, and the exact condition it needs -/

/-- **The degree fact, sharp form (the main theorem of this module).**  Let
`3 ≤ G` and `1 ≤ K < G`, and let three pairwise distinct starts spell the same
length-`K` word.  Then **either** the word carries a maximal triple repeat of
length `≥ K` (which is what violates `Ukkonen`'s triple clause, and is BBT's
contradiction), **or** the circular word has a genuine period `p` with
`0 < p ≤ G`.

The second disjunct is *exactly* the `p = 3` alternative named in
`BBTUniqueEulerian`'s docstring (`S = 012012012`, `G = 9`, `K = 3`), and
§6 characterises it. -/
theorem deg_fact {K : ℕ} (h3 : 3 ≤ G) (hK1 : 1 ≤ K) (hKG : K < G)
    (hex : ∃ a b c : Fin G, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Agr3 hG S a b c K) :
    (∃ a b c : Fin G, ∃ e : Fin G, K ≤ e.val ∧
        (mkGenome hG S).IsTripleRepeat e a b c) ∨
      ∃ p : ℕ, 0 < p ∧ p < G ∧ Period hG S p := by
  obtain ⟨a, b, c, hab, hac, hbc, hag⟩ := hex
  have hne : (span hG S).Nonempty :=
    span_nonempty (hG := hG) (S := S) (K := K) (by omega) ⟨a, b, c, hab, hac, hbc, hag⟩
  have hle : K ≤ spanMax hG S hne := le_spanMax hG S hne
    (mem_span (hG := hG) (S := S) (e := K) (by omega) hab hac hbc hag)
  have hK : 1 ≤ spanMax hG S hne := by omega
  by_cases hlt : spanMax hG S hne < G
  · obtain ⟨a', b', c', e', htr, he'e⟩ :=
      max_span_tripleRepeat (hG := hG) (S := S) (h := hne) hK hlt
    have hK' : K ≤ e'.val := he'e ▸ hle
    exact Or.inl ⟨a', b', c', e', hK', htr⟩
  · obtain ⟨p, hp1, hp2, hper⟩ :=
      max_span_escape (hG := hG) (S := S) (h := hne) (by omega)
    exact Or.inr ⟨p, hp1, hp2, hper⟩

/-- **The source's own statement of the degree fact, under precisely the right
condition.**  If the circular word has no period strictly between `0` and `G`
(`BBTUniqueEulerian.Period`-primitive; equivalently `RepeatAdapter.IsPrimitive`,
see §6), then three pairwise distinct starts spelling the same length-`K` word
force a `Genome.IsTripleRepeat` of length `≥ K`.  This is the sentence
"the cycle `C_0` does not traverse any node three times in `G_0`, for this would
imply the existence of a triple repeat of length `K`". -/
theorem deg_fact_of_primitive {K : ℕ} (h3 : 3 ≤ G) (hK1 : 1 ≤ K) (hKG : K < G)
    (hprim : ∀ d : ℕ, 0 < d → d < G → ¬ Period hG S d)
    (hex : ∃ a b c : Fin G, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Agr3 hG S a b c K) :
    ∃ a b c : Fin G, ∃ e : Fin G, K ≤ e.val ∧
      (mkGenome hG S).IsTripleRepeat e a b c := by
  rcases deg_fact (hG := hG) (S := S) h3 hK1 hKG hex with h | h
  · exact h
  · obtain ⟨p, hp1, hp2, hper⟩ := h
    exact (hprim p hp1 hp2 hper).elim

/-- **The contrapositive, i.e. the multiplicity cap in `BBTUniqueEulerian`
language**: for a primitive word with no maximal triple repeat of length `≥ K`,
no three pairwise distinct starts spell the same length-`K` word. -/
theorem no_three_of_primitive {K : ℕ} (h3 : 3 ≤ G) (hK1 : 1 ≤ K) (hKG : K < G)
    (hprim : ∀ d : ℕ, 0 < d → d < G → ¬ Period hG S d)
    (hno : ¬ ∃ a b c : Fin G, ∃ e : Fin G, K ≤ e.val ∧
      (mkGenome hG S).IsTripleRepeat e a b c) :
    ∀ a b c : Fin G, a ≠ b → a ≠ c → b ≠ c → ¬ Agr3 hG S a b c K := by
  intro a b c hab hac hbc hag
  exact hno (deg_fact_of_primitive (hG := hG) (S := S) h3 hK1 hKG hprim
    ⟨a, b, c, hab, hac, hbc, hag⟩)

/-- Three pairwise distinct members of a finset of cardinality at least `3`. -/
private theorem three_mem_of_card_ge_three {β : Type} [DecidableEq β] {s : Finset β}
    (h : 3 ≤ s.card) :
    ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have hcard1 : 2 ≤ (s.erase a).card := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.mp (by omega : 1 < (s.erase a).card)
  have hbne : b ≠ a := (Finset.mem_erase.mp hb).1
  have hcne : c ≠ a := (Finset.mem_erase.mp hc).1
  exact ⟨a, b, c, ha, Finset.mem_of_mem_erase hb, Finset.mem_of_mem_erase hc,
    hbne.symm, hcne.symm, hbc⟩

/-- Three distinct occurrences of a node, from three distinct members of its
occurrence set: this is `BBTSequenceGraph.deg ≥ 3` read as "the node is
traversed at least three times". -/
theorem three_of_deg_ge_three (K : ℕ) (v : Fin K → α)
    (hv : 3 ≤ deg hG (K + 1) S v) :
    ∃ a b c : Fin G, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      vtx hG (K + 1) S a = v ∧ vtx hG (K + 1) S b = v ∧ vtx hG (K + 1) S c = v := by
  classical
  have hcard : 3 ≤ (Finset.univ.filter
      (fun r : Fin G => vtx hG (K + 1) S r = v)).card := hv
  obtain ⟨r1, r2, r3, hr1, hr2, hr3, h12, h13, h23⟩ :=
    three_mem_of_card_ge_three hcard
  have e1 := (Finset.mem_filter.mp hr1).2
  have e2 := (Finset.mem_filter.mp hr2).2
  have e3 := (Finset.mem_filter.mp hr3).2
  exact ⟨r1, r2, r3, h12, h13, h23, e1, e2, e3⟩

/-- **The degree fact in the out-degree (number of traversals) reading**, which
is how BBT states it: a node of the `(K+1)`-de Bruijn multigraph that is
traversed at least three times forces a maximal triple repeat of length `≥ K`,
provided the word is primitive. -/
theorem deg_fact_node (K : ℕ) (h3 : 3 ≤ G) (hK1 : 1 ≤ K) (hKG : K < G)
    (hprim : ∀ d : ℕ, 0 < d → d < G → ¬ Period hG S d)
    {v : Fin K → α} (hv : 3 ≤ deg hG (K + 1) S v) :
    ∃ a b c : Fin G, ∃ e : Fin G, K ≤ e.val ∧
      (mkGenome hG S).IsTripleRepeat e a b c := by
  obtain ⟨a, b, c, hab, hac, hbc, e1, e2, e3⟩ :=
    three_of_deg_ge_three (hG := hG) (S := S) K v hv
  have hag : Agr3 hG S a b c K := by
    have htmp := vtx_agr3 (hG := hG) (S := S) (L := K + 1) (a := a) (b := b) (c := c)
      (e1.trans e2.symm) (e1.trans e3.symm)
    rwa [Nat.add_sub_cancel] at htmp
  exact deg_fact_of_primitive (hG := hG) (S := S) h3 hK1 hKG hprim
    ⟨a, b, c, hab, hac, hbc, hag⟩

/-! ## 5. The `Ukkonen` and `P2` corollaries -/

/-- **`Ukkonen`'s triple clause, in `BBTUniqueEulerian` vocabulary.**  For a
primitive word, no three pairwise distinct starts spell the same `K`-mer.  This
is the multiplicity content of `BBTUniqueEulerian`'s Lemma 1 ("under `Ukkonen`
every `(L-1)`-mer occurs at most twice"), proved from the degree fact rather
than from `RepeatAdapter`'s two-sided extension engine. -/
theorem no_three_of_Ukkonen_K {K : ℕ} (hKL : K = L - 1) (hK1 : 1 ≤ K) (hKG : K < G)
    (h3 : 3 ≤ G) (hprim : ∀ d : ℕ, 0 < d → d < G → ¬ Period hG S d)
    (hUkk : Ukkonen hG L S) :
    ∀ a b c : Fin G, a ≠ b → a ≠ c → b ≠ c → ¬ Agr3 hG S a b c K := by
  intro a b c hab hac hbc hag
  obtain ⟨a', b', c', e', hK, htr⟩ :=
    deg_fact_of_primitive (hG := hG) (S := S) h3 hK1 hKG hprim
      ⟨a, b, c, hab, hac, hbc, hag⟩
  have hbad : e'.val < L - 1 := hUkk.1 e' a' b' c' htr
  have hle : L - 1 ≤ e'.val := by rw [← hKL]; exact hK
  exact absurd hle (by omega)

/-- **At `K = L - 1`, from `Ukkonen`.** -/
theorem no_three_of_Ukkonen_L (h3 : 3 ≤ G) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hprim : ∀ d : ℕ, 0 < d → d < G → ¬ Period hG S d)
    (hUkk : Ukkonen hG L S) :
    ∀ a b c : Fin G, a ≠ b → a ≠ c → b ≠ c → ¬ Agr3 hG S a b c (L - 1) := by
  intro a b c hab hac hbc hag
  exact no_three_of_Ukkonen_K (hG := hG) (S := S) (L := L) rfl (by omega) (by omega) h3
    hprim hUkk a b c hab hac hbc hag

/-- The same, for the triple clause of `P2`. -/
theorem no_three_of_P2 (h3 : 3 ≤ G) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hprim : ∀ d : ℕ, 0 < d → d < G → ¬ Period hG S d)
    (hP2 : P2 hG L S) :
    ∀ a b c : Fin G, a ≠ b → a ≠ c → b ≠ c → ¬ Agr3 hG S a b c (L - 1) :=
  no_three_of_Ukkonen_L (hG := hG) (S := S) (L := L) h3 hL hLG hprim
    (P2.imp_Ukkonen (hG := hG) (S := S) hL hP2)

/-- The same, in `BBTSequenceGraph.deg` form: every node of the
`(L-1)`-de Bruijn multigraph of a primitive `P2` word is spelled by at most two
starts.  This is `BBTUniqueEulerian`'s Lemma 1, first half, restated; it is
`AssemblyP1.P2.imp_nodeCount_le_two` in the `Fin G → α` word layer, reached
here through the degree fact instead of through `RepeatAdapter.extend_triple`. -/
theorem prim_deg_le_two (h3 : 3 ≤ G) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hprim : ∀ d : ℕ, 0 < d → d < G → ¬ Period hG S d)
    (hP2 : P2 hG L S) (v : Fin (L - 1) → α) : deg hG L S v ≤ 2 := by
  by_contra hgt
  have h3v : 3 ≤ deg hG L S v := by omega
  obtain ⟨a, b, c, hab, hac, hbc, e1, e2, e3⟩ :=
    three_of_deg_ge_three (hG := hG) (S := S) (K := L - 1) v h3v
  have hag : Agr3 hG S a b c (L - 1) :=
    vtx_agr3 (hG := hG) (S := S) (L := (L - 1) + 1) (a := a) (b := b) (c := c) (e1.trans e2.symm) (e1.trans e3.symm)
  exact (no_three_of_P2 (hG := hG) (S := S) (L := L) h3 hL hLG hprim hP2
    a b c hab hac hbc hag)

/-! ## 6. The condition, characterised

The escape disjunct of `deg_fact` occurs exactly when the word is an exact
nontrivial power, i.e. exactly when it is *not* primitive in
`RepeatAdapter.IsPrimitive` sense.  This is a decision procedure:
`leastPeriod hG S < G` is decidable, and so is the whole of `deg_fact`. -/

/-- A genuine period strictly between `0` and `G` exists exactly when the least
period is `< G`. -/
theorem escape_iff_leastPeriod :
    (∃ d : ℕ, 0 < d ∧ d < G ∧ Period hG S d) ↔ leastPeriod hG S < G := by
  constructor
  · rintro ⟨d, h1, h2, h3⟩
    have h3le := leastPeriod_min (hG := hG) (S := S) (d := d) (le_of_lt h2) h1 h3
    exact lt_of_le_of_lt h3le h2
  · intro h
    exact ⟨leastPeriod hG S, (leastPeriod_spec hG S).2.1, h, (leastPeriod_spec hG S).1⟩

/-- `Period d` and `RepeatAdapter.ShiftInvariant d` are the same statement. -/
theorem period_iff_shiftInvariant (d : ℕ) :
    Period hG S d ↔ RepeatAdapter.ShiftInvariant hG S d := by
  constructor
  · intro h i
    have h1 : rotAdd hG d ⟨i % G, Nat.mod_lt _ hG⟩ = ⟨(i + d) % G, Nat.mod_lt _ hG⟩ := by
      apply Fin.ext
      exact (mod_add_shl i d).symm
    have h2 := h ⟨i % G, Nat.mod_lt _ hG⟩
    rw [h1] at h2
    exact h2.symm
  · intro h r
    have h1 := h r.val
    have h2 : cyc hG S (r.val + d) = S (rotAdd hG d r) := rfl
    have h3 : cyc hG S r.val = S r := by
      unfold cyc
      congr 1
      apply Fin.ext
      exact Nat.mod_eq_of_lt r.isLt
    rw [h2, h3] at h1
    exact h1.symm

/-- So the escape disjunct of `deg_fact` occurs exactly when `S` is **not**
primitive in the shift sense. -/
theorem escape_iff_not_IsPrimitive :
    (∃ d : ℕ, 0 < d ∧ d < G ∧ Period hG S d) ↔ ¬ RepeatAdapter.IsPrimitive hG S := by
  constructor
  · rintro ⟨d, h1, h2, hper⟩ hprim
    exact hprim d h1 h2 ((period_iff_shiftInvariant hG S d).mp hper)
  · intro hn
    by_cases hex : ∃ d : ℕ, 0 < d ∧ d < G ∧ RepeatAdapter.ShiftInvariant hG S d
    · obtain ⟨d, h1, h2, hsi⟩ := hex
      exact ⟨d, h1, h2, (period_iff_shiftInvariant hG S d).mpr hsi⟩
    · exact (hn (fun d hd1 hd2 hsi => (hex ⟨d, hd1, hd2, hsi⟩).elim)).elim

/-- **The degree fact, decided.**  For `3 ≤ G`, `1 ≤ K < G` and no maximal
triple repeat of length `≥ K`, three distinct starts spelling the same
length-`K` word force a nontriv period; equivalently, on a primitive word no
such triple exists at all.  This is the statement the next front can instantiate
at `K = L - 1`. -/
theorem deg_fact_escape_only {K : ℕ} (h3 : 3 ≤ G) (hK1 : 1 ≤ K) (hKG : K < G)
    (hno : ¬ ∃ a b c : Fin G, ∃ e : Fin G, K ≤ e.val ∧
      (mkGenome hG S).IsTripleRepeat e a b c)
    (hex : ∃ a b c : Fin G, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Agr3 hG S a b c K) :
    ∃ d : ℕ, 0 < d ∧ d < G ∧ Period hG S d := by
  rcases deg_fact (hG := hG) (S := S) h3 hK1 hKG hex with h | h
  · exact absurd h hno
  · obtain ⟨p, hp1, hp2, hper⟩ := h
    exact ⟨p, hp1, by omega, hper⟩

/-! ## 7. The unrestricted form is false: a kernel-checked counterexample

`S = 012012012`, `G = 9`, `K = 3`.  The three starts `0, 3, 6` all spell the
length-`3` word `012`, so the node `012` of the `4`-mer multigraph is traversed
three times; and at those three starts there is **no** maximal triple repeat at
any of the three lengths checked (`e = 3`, `4`, `8`), so the `Ukkonen` triple
clause and the `P2` triple clause both hold on this instance.  The
unrestricted degree fact is therefore false, and `escape_iff_leastPeriod`
explains the instance: the least period is `3 < 9`.

**Scope limit, stated precisely (review finding 1).**  What this section
proves is `¬ IsTripleRepeat e 0 3 6` at `e = 3`, `4`, `8` — **one triple, three
lengths**.  It does **not** prove the global statement "`012012012` has no
maximal triple repeat at any length, at any triple", which is probably true
but is not in this file.  The other lengths (`0, 1, 2, 5, 6, 7` at that triple)
and all other triples are unchecked.  A reader wanting the global statement
must either fix the `Decidable` instance search for the `∀`/`∃` over `Fin 9`
or prove it by hand. -/

/-- `S = 012012012` on the circle of length `9`. -/
def S9 : Fin 9 → Bool :=
  ![true, false, false, true, false, false, true, false, false]

theorem hG9 : (0 : ℕ) < 9 := by norm_num

/-- `Genome.Agree` is decidable at these concrete sizes (a `∀` over a finite
`Fin e` of decidable equalities); this is an instance for the *counterexample*
word only; no definition is changed. -/
instance decAgree9 (e : ℕ) (a b : Fin 9) :
    Decidable ((mkGenome hG9 S9).Agree e a b) := by
  unfold SourceFaithfulIs.Genome.Agree
  infer_instance

/-- `IsTripleRepeat` is decidable at these concrete sizes, which is what the
counterexamples below need.  This is an instance for the *counterexample* word
only; no definition is changed.  (The `show` is needed because instance
synthesis on the unfolded conjunction is fragile in this pin; the `e a b c` are
all concrete, which is what the counterexamples use.) -/
instance decIsTripleRepeat9 (e : ℕ) (a b c : Fin 9) :
    Decidable ((mkGenome hG9 S9).IsTripleRepeat e a b c) := by
  show Decidable (1 ≤ e ∧ e < (mkGenome hG9 S9).len ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (mkGenome hG9 S9).Agree e a b ∧ (mkGenome hG9 S9).Agree e a c ∧
      (mkGenome hG9 S9).Agree e b c ∧
      ¬((mkGenome hG9 S9).Preceding a = (mkGenome hG9 S9).Preceding b ∧
        (mkGenome hG9 S9).Preceding b = (mkGenome hG9 S9).Preceding c) ∧
      ¬((mkGenome hG9 S9).Following e a = (mkGenome hG9 S9).Following e b ∧
        (mkGenome hG9 S9).Following e b = (mkGenome hG9 S9).Following e c))
  infer_instance

/-- The length-`3` words at the starts `0, 3, 6` are all `012`: the node `012`
is spelled by three distinct starts. -/
theorem vtx9_three :
    vtx hG9 4 S9 (0 : Fin 9) = ![true, false, false] ∧
      vtx hG9 4 S9 (3 : Fin 9) = ![true, false, false] ∧
      vtx hG9 4 S9 (6 : Fin 9) = ![true, false, false] := by
  decide +kernel

/-- The out-degree of the node `012` is exactly `3`: it is traversed three
times, and by no more. -/
theorem deg9_012 : deg hG9 4 S9 ![true, false, false] = 3 := by
  decide +kernel

/-- **The refutation of the unrestricted form, kernel-checked.**  The three
distinct starts `0, 3, 6` all spell the length-`3` word `012`
(`vtx9_three`), the node `012` is therefore spelled by exactly three starts and
so is traversed three times (`deg9_012`), and yet the triple of its occurrences
is **not** a `Genome.IsTripleRepeat` of length `3`.  So "a node traversed three
times forces a maximal triple repeat of length `≥ K`" is false, at
`K = 3 < 9 = G`, and the word is not primitive (`not_IsPrimitive9`): the
counterexample is exactly the escape disjunct of `deg_fact`. -/
theorem no_tripleRepeat_012012012 :
    ¬ (mkGenome hG9 S9).IsTripleRepeat 3 (0 : Fin 9) (3 : Fin 9) (6 : Fin 9) := by
  decide +kernel

/-- The same at length `4` (so the failure is not an artefact of the length). -/
theorem no_tripleRepeat4_012012012 :
    ¬ (mkGenome hG9 S9).IsTripleRepeat 4 (0 : Fin 9) (3 : Fin 9) (6 : Fin 9) := by
  decide +kernel

/-- And at length `8`, the largest that fits. -/
theorem no_tripleRepeat8_012012012 :
    ¬ (mkGenome hG9 S9).IsTripleRepeat 8 (0 : Fin 9) (3 : Fin 9) (6 : Fin 9) := by
  decide +kernel

/-- The least period of `012012012` is `3 < 9`, which is exactly the escape
disjunct of `deg_fact`. -/
theorem leastPeriod9 : leastPeriod hG9 S9 = 3 := by
  decide +kernel

/-- And `3` is a genuine period below `G = 9`, i.e. the escape really fires. -/
theorem period3_9 : Period hG9 S9 3 ∧ (0 : ℕ) < 3 ∧ 3 < 9 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  decide +kernel

/-- The word is not primitive in the shift sense, as it must be. -/
theorem not_IsPrimitive9 : ¬ RepeatAdapter.IsPrimitive hG9 S9 := by
  intro h
  exact h 3 (by norm_num) (by norm_num)
    ((period_iff_shiftInvariant hG9 S9 3).mp period3_9.1)

end AssemblyP1.Issue94TW6Lemma1
