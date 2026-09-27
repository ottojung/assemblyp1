import AssemblyP1.P2
import AssemblyP1.BBTCondense

/-!
# The maximal-extension bridge from branch occurrences to maximal repeats (#89)

_This module proves step 2 of the reduction isolated in
`docs/bbt-eulerian-cycle-89.md` §6.  Step 1 (condensation bookkeeping) and
the objects of `AssemblyP1.BBTEulerian` are already in the kernel; step 3
(the dichotomy) is not attempted here.  See §6 of this file for exactly what
is and is not proved._

## The gap being bridged

`AssemblyP1.BBTCondense` gives the condensed objects of `thm:BBT`: the
`(L-1)`-mers of the truth, the multiplicity `deg`, and `Branch v := 2 ≤ deg v`
(§1 there).  `AssemblyP1.P2` / `def:P1P2` ranges over a different object
entirely: `Genome.IsRepeat`, a *maximal* two-sided repeat, with
`Preceding a ≠ Preceding b` and `Following e a ≠ Following e b`.

So an alternative Eulerian cycle of the condensed graph is a statement about
*raw* repeated `(L-1)`-mer occurrences, while `EulerianCycleObstruction` is a
statement about *maximal* repeats.  This module proves the bridge between the
two: a raw repeated occurrence extends to a maximal repeat of the truth whose
length is `≥ L - 1`.

This is precisely the step that **cannot** be replaced by "`raw` node pairs
are maximal repeats": `AssemblyP1.BBTChords.raw_node_crossing_not_maximal` is
the kernel-checked counterexample, and
`docs/audit-p2-direct-proof-maximal-extension-2026-09-21.md` gives the exact
word (`S = AABCBCBAB`, `L = 3`) at which a raw pair extends to a *longer*
maximal repeat.  The raw pair is only a **seed**: the extension below is
genuinely two-sided, and its length is whatever maximality forces, not
`L - 1`.

## Where primitivity enters, and only there

`Genome.IsRepeat` requires `e < G`.  This is the only place the argument can
fail, and it is exactly where primitivity is used: if the two-sided extension
of two occurrences in distinct residue classes ever reached length `G`, the
two copies would agree on `G` consecutive positions, i.e. on a whole turn of
the circle, which forces invariance under a nonzero shift --- precisely
`AssemblyP1.RepeatAdapter.not_primitive_of_ge_G_agree`, already proved in the
kernel.

The two maxima are taken over `Finset.range G`, so each *one-sided* extension
is bounded by construction; primitivity is needed only at the boundary case
`ℓ + 1 = G` (resp. `r + 1 = G`), where the extension has reached a full turn
and the two copies would coincide all the way round.  Concretely, primitivity
is used in exactly three places, and nowhere else:

* `no_left_ext_of_G`, at the boundary `ℓ + 1 = G` in `exists_maxLeft`: this is
  the only way a left extension can leave the search range `0 ≤ k < G`;
* `no_right_ext_of_G`, at the boundary `r + 1 = G` in `exists_maxRight`, the
  same for the right extension;
* `maximal_extension_of_repeated`, step `heG`: the **joint** bound
  `ℓ + (L-1) + r < G`.  Neither `ℓ < G` nor `r < G` suffices, and this is
  where the *combined* copy matters: the extended pair agrees on
  `ℓ + (L-1) + r` consecutive positions, so a combined length `≥ G` again
  forces shift-invariance.

`docs/bbt-eulerian-cycle-89.md` §6 flagged exactly this: *"Step 2 needs
primitivity of the truth to keep the maximal extension below `G` …; the BBT
step is applied to the truth alone, so a primitivity hypothesis has to be
threaded into `BBTCompleteSpectrumUniqueness` or an extension bound proved
directly."*  This module proves the extension bound, under primitivity stated
as an explicit hypothesis of the bridge lemma.  It deliberately does **not**
restate `EulerianCycleObstruction` with a primitivity hypothesis added; see §6.

## What is proved here, and what is not

* **Proved (kernel-checked).**  `maximal_extension_of_repeated`: a raw
  repeated `(L-1)`-mer occurrence of the truth, at two distinct positions of a
  primitive truth, lies inside a **maximal** repeat of length `e ≥ L - 1`
  with `e < G`; the two starts of that maximal repeat are the two occurrences
  shifted left by the same amount.  `Branch_of_vtx_eq_ne` shows the input is
  genuinely a branch object of the condensation.
* **Not proved.**  The dichotomy (step 3 of `docs/bbt-eulerian-cycle-89.md` §6):
  that a genuinely distinct Eulerian cycle supplies either a maximal *triple*
  repeat or two interleaved maximal repeats.  `EulerianCycleObstruction` is
  therefore still open, and `AssemblyP1.P2.BBTUniqueAt` remains derived in
  the population chain from it as an explicit hypothesis.  No `sorry`, no
  `admit`, no new axiom.

Nothing here assumes `NodeCrossing` or any raw chord-laminarity statement;
both are known false (`BBTChords` §5, `BBTChords.raw_node_crossing_not_maximal`)
and are not used.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace AssemblyP1.P2RepeatResidual

open SourceFaithfulIs
open OrientedRigidity
open AssemblyP1.RepeatAdapter
open AssemblyP1.BBTSequenceGraph
open AssemblyP1

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-! ## 1. Small helpers

Everything below is stated on the residues `A`, `B` of the two occurrences
with `G` as modulus, so that no `Fin` index arithmetic enters the definitions
and no negative offsets appear: for `d < k ≤ G` and `A ≥ 0` the position
`A + G - 1 - d` is a genuine nonneg index reading the position `A - 1 - d`
around the circle. -/

/-- `cyc` depends only on its argument modulo `G`.  (A local copy of
`AssemblyP1.RepeatAdapter.cyc_congr`, which is `private` there.) -/
theorem cyc_congr' {G : ℕ} (hG : 0 < G) (S : Fin G → α) {x y : ℕ}
    (h : x % G = y % G) : cyc hG S x = cyc hG S y := by
  unfold cyc
  exact congrArg S (Fin.ext h)

/-- `(x + G) % G = x % G`, the residue form. -/
theorem add_G_mod' {G : ℕ} (x : ℕ) : (x + G) % G = x % G := by
  rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]

/-- `Genome.cycl` of the truth, read at an integer position, is `cyc` of the
truth.  This is what lets the `Genome.IsRepeat` maximality conditions be
discharged as congruence statements about `cyc`. -/
theorem Genome_cycl_eq_cyc (hG : 0 < G) (S : Fin G → α) (i : ℕ) :
    Genome.cycl (mkGenome hG S) i = cyc hG S i := rfl

/-- **Cancelling a common shift in a residue comparison.**  Shifting both
positions by the same amount and reducing modulo `G` does not change whether
the two residues agree; this is what lets `not_right_ext_of_G` be used with the
offset `n = L - 1` while only the *unshifted* residues are known to differ. -/
theorem mod_add_cancel_right {G c x y : ℕ} (h : (x + c) % G = (y + c) % G) :
    x % G = y % G :=
  Nat.ModEq.add_right_cancel' c h

/-- The `k` positions immediately preceding `A` agree with those preceding
`B`.  For `k ≤ G` the index `A + G - 1 - d` is the position `A - 1 - d`. -/
def LeftAgree (hG : 0 < G) (S : Fin G → α) (A B k : ℕ) : Prop :=
  ∀ d : ℕ, d < k → cyc hG S (A + G - 1 - d) = cyc hG S (B + G - 1 - d)

/-- The `k` positions from `A + n` onwards agree with those from `B + n`. -/
def RightAgree (hG : 0 < G) (S : Fin G → α) (A B n k : ℕ) : Prop :=
  ∀ d : ℕ, d < k → cyc hG S (A + n + d) = cyc hG S (B + n + d)

instance (hG : 0 < G) (S : Fin G → α) (A B k : ℕ) :
    Decidable (LeftAgree hG S A B k) := by unfold LeftAgree; infer_instance

instance (hG : 0 < G) (S : Fin G → α) (A B n k : ℕ) :
    Decidable (RightAgree hG S A B n k) := by unfold RightAgree; infer_instance

/-- **Left agreement is downward closed:** a sub-window of an agreeing window
agrees.  This is what makes the maximum below carry a maximality statement. -/
theorem LeftAgree_mono {hG : 0 < G} {S : Fin G → α} {A B k k' : ℕ}
    (h : LeftAgree hG S A B k) (hkk' : k' ≤ k) : LeftAgree hG S A B k' := by
  intro d hd
  have hdk : d < k := by omega
  exact h d hdk

/-- **Right agreement is downward closed.** -/
theorem RightAgree_mono {hG : 0 < G} {S : Fin G → α} {A B n k k' : ℕ}
    (h : RightAgree hG S A B n k) (hkk' : k' ≤ k) : RightAgree hG S A B n k' := by
  intro d hd
  have hdk : d < k := by omega
  exact h d hdk

/-- Reading the circle from the extended start `A' = (A + G - ℓ) % G` at
offset `d` reads the same position as `A + G - ℓ + d`.  This is the only
congruence the bridge needs. -/
theorem cyc_shift {G : ℕ} {A' A ℓ d : ℕ} (hA' : A' % G = (A + G - ℓ) % G) :
    (A' + d) % G = (A + G - ℓ + d) % G :=
  Nat.add_mod_eq_add_mod_right d hA'

/-- **The pointwise consequence of left maximality.**  If agreement holds
for the `ℓ` positions preceding `A` and `B` but fails for the `ℓ + 1`
positions, then it fails exactly at the `ℓ`-th position: the predecessor
symbols of `A` and `B` differ.  (The witness of the failure is forced to be
`d = ℓ`, because every `d < ℓ` is covered by `h`.) -/
theorem LeftAgree_not_succ {hG : 0 < G} {S : Fin G → α} {A B ℓ : ℕ}
    (h : LeftAgree hG S A B ℓ) (hn : ¬ LeftAgree hG S A B (ℓ + 1)) :
    cyc hG S (A + G - 1 - ℓ) ≠ cyc hG S (B + G - 1 - ℓ) := by
  have hnot : ¬ ∀ d : ℕ, d < ℓ + 1 →
      cyc hG S (A + G - 1 - d) = cyc hG S (B + G - 1 - d) := hn
  push Not at hnot
  obtain ⟨d, hdle, hne⟩ := hnot
  have hdl : d = ℓ := by
    by_contra hc
    exact absurd (h d (by omega)) hne
  exact hdl ▸ hne

/-- **The pointwise consequence of right maximality.**  Likewise, the symbols
following the length-`(n + r)` copies differ. -/
theorem RightAgree_not_succ {hG : 0 < G} {S : Fin G → α} {A B n r : ℕ}
    (h : RightAgree hG S A B n r) (hn : ¬ RightAgree hG S A B n (r + 1)) :
    cyc hG S (A + n + r) ≠ cyc hG S (B + n + r) := by
  have hnot : ¬ ∀ d : ℕ, d < r + 1 →
      cyc hG S (A + n + d) = cyc hG S (B + n + d) := hn
  push Not at hnot
  obtain ⟨d, hdle, hne⟩ := hnot
  have hdl : d = r := by
    by_contra hc
    exact absurd (h d (by omega)) hne
  exact hdl ▸ hne

/-! ## 2. Primitivity forbids an extension of a full turn -/

/-- **A left extension of a full turn contradicts primitivity.**  Agreement on
the `G` positions preceding `A` and `B` is, after re-indexing by
`i = G - 1 - d`, agreement on the `G` positions *starting* at `A` and `B`;
the residues are distinct, so `not_primitive_of_ge_G_agree` applies. -/
theorem no_left_ext_of_G {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B : ℕ}
    (hAB : A % G ≠ B % G) (h : LeftAgree hG S A B G)
    (hprim : IsPrimitive hG S) : False := by
  have hag : ∀ d : ℕ, d < G → cyc hG S (A + d) = cyc hG S (B + d) := by
    intro d hd
    have hd' : G - 1 - d < G := by omega
    have hdd := h (G - 1 - d) hd'
    have e1 : A + G - 1 - (G - 1 - d) = A + d := by omega
    have e2 : B + G - 1 - (G - 1 - d) = B + d := by omega
    rw [e1, e2] at hdd
    exact hdd
  exact not_primitive_of_ge_G_agree hG S A B G hAB (le_refl G) hag hprim

/-- **A right extension of a full turn contradicts primitivity.**  No
re-indexing is needed: `RightAgree n G` is directly a whole-turn agreement
between the distinct residues `A + n` and `B + n`. -/
theorem no_right_ext_of_G {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B n : ℕ}
    (hAB : (A + n) % G ≠ (B + n) % G) (h : RightAgree hG S A B n G)
    (hprim : IsPrimitive hG S) : False :=
  not_primitive_of_ge_G_agree hG S (A + n) (B + n) G hAB (le_refl G) h hprim

/-! ## 3. The two maximal extensions -/

/-- The left extension amounts available: `0 ≤ k ≤ G` with `LeftAgree k`. -/
def leftExt (hG : 0 < G) (S : Fin G → α) (A B : ℕ) : Finset ℕ :=
  (Finset.range G).filter (LeftAgree hG S A B)

/-- The right extension amounts available: `0 ≤ k ≤ G` with `RightAgree n k`. -/
def rightExt (hG : 0 < G) (S : Fin G → α) (A B n : ℕ) : Finset ℕ :=
  (Finset.range G).filter (RightAgree hG S A B n)

theorem zero_mem_leftExt (hG : 0 < G) (S : Fin G → α) (A B : ℕ) :
    0 ∈ leftExt hG S A B := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
  intro d hd
  omega

theorem zero_mem_rightExt (hG : 0 < G) (S : Fin G → α) (A B n : ℕ) :
    0 ∈ rightExt hG S A B n := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
  intro d hd
  omega

theorem leftExt_nonempty (hG : 0 < G) (S : Fin G → α) (A B : ℕ) :
    (leftExt hG S A B).Nonempty :=
  ⟨0, zero_mem_leftExt hG S A B⟩

theorem rightExt_nonempty (hG : 0 < G) (S : Fin G → α) (A B n : ℕ) :
    (rightExt hG S A B n).Nonempty :=
  ⟨0, zero_mem_rightExt hG S A B n⟩

/-- **The left extension cannot reach a full turn**, so the maximum of
`leftExt` is below `G`. -/
theorem not_mem_leftExt_G {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B : ℕ}
    (hAB : A % G ≠ B % G) (hprim : IsPrimitive hG S) : G ∉ leftExt hG S A B := by
  intro hmem
  exact (no_left_ext_of_G hG S hAB (Finset.mem_filter.mp hmem).2 hprim).elim

/-- Likewise for the right extension. -/
theorem not_mem_rightExt_G {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B n : ℕ}
    (hAB : (A + n) % G ≠ (B + n) % G) (hprim : IsPrimitive hG S) : G ∉ rightExt hG S A B n := by
  intro hmem
  exact (no_right_ext_of_G hG S hAB (Finset.mem_filter.mp hmem).2 hprim).elim

/-- **The maximal left extension exists, is shorter than a full turn, and is
not extendable by one symbol.**  The last clause is the left half of the
maximality of the resulting `Genome.IsRepeat`. -/
theorem exists_maxLeft {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B : ℕ}
    (hAB : A % G ≠ B % G) (hprim : IsPrimitive hG S) :
    ∃ ℓ : ℕ, ℓ < G ∧ LeftAgree hG S A B ℓ ∧ ¬ LeftAgree hG S A B (ℓ + 1) := by
  have hne := leftExt_nonempty hG S A B
  have hmax : (leftExt hG S A B).max' hne ∈ leftExt hG S A B := Finset.max'_mem _ _
  have hmax_lt : (leftExt hG S A B).max' hne < G :=
    Finset.mem_range.mp (Finset.mem_filter.mp hmax).1
  have hmax_bound : ∀ k ∈ leftExt hG S A B, k ≤ (leftExt hG S A B).max' hne :=
    fun k hk => Finset.le_max' _ _ hk
  have hLag : LeftAgree hG S A B ((leftExt hG S A B).max' hne) :=
    (Finset.mem_filter.mp hmax).2
  refine ⟨(leftExt hG S A B).max' hne, hmax_lt, hLag, ?_⟩
  intro hc
  by_cases hlt : (leftExt hG S A B).max' hne + 1 < G
  · have hmem1 : (leftExt hG S A B).max' hne + 1 ∈ leftExt hG S A B := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hc⟩
    have h1 := hmax_bound ((leftExt hG S A B).max' hne + 1) hmem1
    omega
  · -- `ℓ + 1 = G`: a left extension of a full turn, ruled out by primitivity
    have he : (leftExt hG S A B).max' hne + 1 = G := by omega
    have h1 : LeftAgree hG S A B G := Eq.mp (congrArg (fun k : ℕ => LeftAgree hG S A B k) he) hc
    exact (no_left_ext_of_G hG S hAB h1 hprim).elim

/-- **The maximal right extension exists, is shorter than a full turn, and is
not extendable by one symbol.**  The last clause is the right half of the
maximality of the resulting `Genome.IsRepeat`. -/
theorem exists_maxRight {G : ℕ} (hG : 0 < G) (S : Fin G → α) {A B n : ℕ}
    (hAB : (A + n) % G ≠ (B + n) % G) (hprim : IsPrimitive hG S) :
    ∃ r : ℕ, r < G ∧ RightAgree hG S A B n r ∧ ¬ RightAgree hG S A B n (r + 1) := by
  have hne := rightExt_nonempty hG S A B n
  have hmax : (rightExt hG S A B n).max' hne ∈ rightExt hG S A B n := Finset.max'_mem _ _
  have hmax_lt : (rightExt hG S A B n).max' hne < G :=
    Finset.mem_range.mp (Finset.mem_filter.mp hmax).1
  have hmax_bound : ∀ k ∈ rightExt hG S A B n, k ≤ (rightExt hG S A B n).max' hne :=
    fun k hk => Finset.le_max' _ _ hk
  have hRag : RightAgree hG S A B n ((rightExt hG S A B n).max' hne) :=
    (Finset.mem_filter.mp hmax).2
  refine ⟨(rightExt hG S A B n).max' hne, hmax_lt, hRag, ?_⟩
  intro hc
  by_cases hlt : (rightExt hG S A B n).max' hne + 1 < G
  · have hmem1 : (rightExt hG S A B n).max' hne + 1 ∈ rightExt hG S A B n := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hc⟩
    have h1 := hmax_bound ((rightExt hG S A B n).max' hne + 1) hmem1
    omega
  · -- `r + 1 = G`: a right extension of a full turn, ruled out by primitivity
    have he : (rightExt hG S A B n).max' hne + 1 = G := by omega
    have h1 : RightAgree hG S A B n G :=
      Eq.mp (congrArg (fun k : ℕ => RightAgree hG S A B n k) he) hc
    exact (no_right_ext_of_G hG S hAB h1 hprim).elim

/-! ## 4. The bridge lemma -/

/-- **The maximal-extension bridge (step 2 of #89).**  A *raw* repeated
`(L-1)`-mer occurrence of a primitive truth --- two distinct starts spelling
the same `(L-1)`-mer, i.e. a branch occurrence of the condensation --- lies
inside a **maximal** repeat of the truth of length `e` with
`L - 1 ≤ e < G`.

The two starts of that maximal repeat are the two occurrences shifted left by
the *same* amount, which is what makes the resulting `Genome.IsRepeat` well
formed.  The amount is `ℓ`, the maximal left extension of §3, and
`e = ℓ + (L-1) + r` with `r` the maximal right extension.  `e < G` is the
step in which primitivity is used. -/
theorem maximal_extension_of_repeated {G : ℕ} (hG : 0 < G) {L : ℕ} (hL : 2 ≤ L)
    (S : Fin G → α) {a b : Fin G} (hne : a ≠ b) (hvtx : vtx hG L S a = vtx hG L S b)
    (hprim : IsPrimitive hG S) :
    ∃ (e : ℕ) (a' b' : Fin G),
      L - 1 ≤ e ∧ e < G ∧ a' ≠ b' ∧ (mkGenome hG S).IsRepeat e a' b' := by
  have hnpos : 1 ≤ L - 1 := by omega
  have hAB : a.val % G ≠ b.val % G := by
    intro h
    exact hne (Fin.ext ((Nat.mod_eq_of_lt a.isLt).symm.trans
      (h.trans (Nat.mod_eq_of_lt b.isLt))))
  -- the seed: the two occurrences spell the same `(L-1)`-mer
  have hag : ∀ d : ℕ, d < L - 1 → cyc hG S (a.val + d) = cyc hG S (b.val + d) := by
    intro d hd
    have hv := congrFun hvtx (⟨d, hd⟩ : Fin (L - 1))
    simpa only [vtx, nodeWindow, cyc] using hv
  obtain ⟨ℓ, hℓG, hLag, hLag'⟩ := exists_maxLeft hG S hAB hprim
  have hABn : (a.val + (L - 1)) % G ≠ (b.val + (L - 1)) % G := by
    intro h
    exact hAB (mod_add_cancel_right h)
  obtain ⟨r, hrG, hRag, hRag'⟩ := exists_maxRight hG S hABn hprim
  -- the extended starts are the two occurrences shifted left by `ℓ`
  have hA'lt : (a.val + G - ℓ) % G < G := Nat.mod_lt _ hG
  have hB'lt : (b.val + G - ℓ) % G < G := Nat.mod_lt _ hG
  have hAl : ((a.val + G - ℓ) % G + ℓ) % G = a.val % G := by
    rw [Nat.add_mod_eq_add_mod_right ℓ (Nat.mod_mod (a.val + G - ℓ) G),
      show a.val + G - ℓ + ℓ = a.val + G from by omega, add_G_mod']
  have hBl : ((b.val + G - ℓ) % G + ℓ) % G = b.val % G := by
    rw [Nat.add_mod_eq_add_mod_right ℓ (Nat.mod_mod (b.val + G - ℓ) G),
      show b.val + G - ℓ + ℓ = b.val + G from by omega, add_G_mod']
  have hA'B'mod : (a.val + G - ℓ) % G ≠ (b.val + G - ℓ) % G := by
    intro h
    have h1 : ((a.val + G - ℓ) % G + ℓ) % G = ((b.val + G - ℓ) % G + ℓ) % G :=
      congrArg (fun t : ℕ => (t + ℓ) % G) h
    exact hAB (hAl.symm.trans (h1.trans hBl))
  -- the combined copies agree on `e = ℓ + (L - 1) + r` consecutive positions
  have hag' : ∀ d : ℕ, d < ℓ + (L - 1) + r →
      cyc hG S ((a.val + G - ℓ) % G + d) = cyc hG S ((b.val + G - ℓ) % G + d) := by
    intro d hd
    have hdA : ((a.val + G - ℓ) % G + d) % G = (a.val + G - ℓ + d) % G :=
      Nat.add_mod_eq_add_mod_right d (Nat.mod_mod (a.val + G - ℓ) G)
    have hdB : ((b.val + G - ℓ) % G + d) % G = (b.val + G - ℓ + d) % G :=
      Nat.add_mod_eq_add_mod_right d (Nat.mod_mod (b.val + G - ℓ) G)
    rw [cyc_congr' hG S hdA, cyc_congr' hG S hdB]
    by_cases hd1 : d < ℓ
    · -- inside the maximal left extension
      have hd' : ℓ - 1 - d < ℓ := by omega
      have h := hLag (ℓ - 1 - d) hd'
      calc cyc hG S (a.val + G - ℓ + d)
          = cyc hG S (a.val + G - 1 - (ℓ - 1 - d)) := by rw [show
              a.val + G - ℓ + d = a.val + G - 1 - (ℓ - 1 - d) from by omega]
        _ = cyc hG S (b.val + G - 1 - (ℓ - 1 - d)) := h
        _ = cyc hG S (b.val + G - ℓ + d) := by rw [show
              b.val + G - 1 - (ℓ - 1 - d) = b.val + G - ℓ + d from by omega]
    · by_cases hd2 : d < ℓ + (L - 1)
      · -- inside the seed
        have hd' : d - ℓ < L - 1 := by omega
        calc cyc hG S (a.val + G - ℓ + d)
            = cyc hG S ((a.val + (d - ℓ)) + G) := by rw [show
                a.val + G - ℓ + d = (a.val + (d - ℓ)) + G from by omega]
          _ = cyc hG S (a.val + (d - ℓ)) := cyc_congr' hG S (add_G_mod' _)
          _ = cyc hG S (b.val + (d - ℓ)) := hag _ hd'
          _ = cyc hG S (b.val + G - ℓ + d) := by rw [show
                b.val + G - ℓ + d = (b.val + (d - ℓ)) + G from by omega,
              ← cyc_congr' hG S (add_G_mod' _)]
      · -- inside the maximal right extension
        have hd' : d - (ℓ + (L - 1)) < r := by omega
        calc cyc hG S (a.val + G - ℓ + d)
            = cyc hG S ((a.val + (L - 1) + (d - (ℓ + (L - 1)))) + G) := by rw [show
                a.val + G - ℓ + d = (a.val + (L - 1) + (d - (ℓ + (L - 1)))) + G
                  from by omega]
          _ = cyc hG S (a.val + (L - 1) + (d - (ℓ + (L - 1)))) :=
            cyc_congr' hG S (add_G_mod' _)
          _ = cyc hG S (b.val + (L - 1) + (d - (ℓ + (L - 1)))) := hRag _ hd'
          _ = cyc hG S (b.val + G - ℓ + d) := by rw [show
                b.val + G - ℓ + d = (b.val + (L - 1) + (d - (ℓ + (L - 1)))) + G
                  from by omega,
              ← cyc_congr' hG S (add_G_mod' _)]
  -- **primitivity bounds the combined extension**
  have heG : ℓ + (L - 1) + r < G := by
    by_contra hcon
    have heG' : G ≤ ℓ + (L - 1) + r := by omega
    exact not_primitive_of_ge_G_agree hG S ((a.val + G - ℓ) % G) ((b.val + G - ℓ) % G)
      (ℓ + (L - 1) + r) (by simpa only [Nat.mod_mod] using hA'B'mod) heG' hag' hprim
  have hA'B'Fin : (⟨(a.val + G - ℓ) % G, hA'lt⟩ : Fin G) ≠ ⟨(b.val + G - ℓ) % G, hB'lt⟩ := by
    intro h
    have h1 := congrArg Fin.val h
    exact hA'B'mod h1
  refine ⟨ℓ + (L - 1) + r, ⟨(a.val + G - ℓ) % G, hA'lt⟩, ⟨(b.val + G - ℓ) % G, hB'lt⟩,
    by omega, heG, hA'B'Fin, ?_⟩
  refine ⟨?_, heG, ?_, ?_, ?_⟩
  · have h1 : 1 ≤ ℓ + (L - 1) + r := by omega
    exact h1
  · exact hA'B'Fin
  · -- `Agree e a' b'`
    intro d
    have hd' : d.val < ℓ + (L - 1) + r := d.isLt
    have h := hag' d.val hd'
    show cyc hG S ((a.val + G - ℓ) % G + d.val) = cyc hG S ((b.val + G - ℓ) % G + d.val)
    exact h
  · refine ⟨?_, ?_⟩
    · -- `Preceding a' ≠ Preceding b'`: maximality of the left extension
      have hneP : cyc hG S (a.val + G - 1 - ℓ) ≠ cyc hG S (b.val + G - 1 - ℓ) :=
        LeftAgree_not_succ hLag hLag'
      intro hc
      apply hneP
      have h3' : cyc hG S ((a.val + G - ℓ) % G + G - 1)
          = cyc hG S ((b.val + G - ℓ) % G + G - 1) := by
        show Genome.cycl (mkGenome hG S) ((a.val + G - ℓ) % G + G - 1)
          = Genome.cycl (mkGenome hG S) ((b.val + G - ℓ) % G + G - 1)
        exact hc
      have h1 : cyc hG S ((a.val + G - ℓ) % G + G - 1)
          = cyc hG S (a.val + G - 1 - ℓ) := by
        refine cyc_congr' hG S ?_
        have h2 := Nat.add_mod_eq_add_mod_right (G - 1) (Nat.mod_mod (a.val + G - ℓ) G)
        rw [show (a.val + G - ℓ) % G + (G - 1) = (a.val + G - ℓ) % G + G - 1 from by omega,
          show a.val + G - ℓ + (G - 1) = (a.val + G - 1 - ℓ) + G from by omega,
          add_G_mod'] at h2
        exact h2
      have h2' : cyc hG S ((b.val + G - ℓ) % G + G - 1)
          = cyc hG S (b.val + G - 1 - ℓ) := by
        refine cyc_congr' hG S ?_
        have h2 := Nat.add_mod_eq_add_mod_right (G - 1) (Nat.mod_mod (b.val + G - ℓ) G)
        rw [show (b.val + G - ℓ) % G + (G - 1) = (b.val + G - ℓ) % G + G - 1 from by omega,
          show b.val + G - ℓ + (G - 1) = (b.val + G - 1 - ℓ) + G from by omega,
          add_G_mod'] at h2
        exact h2
      exact h1.symm.trans (h3'.trans h2')
    · -- `Following e a' ≠ Following e b'`: maximality of the right extension
      have hneF : cyc hG S (a.val + (L - 1) + r) ≠ cyc hG S (b.val + (L - 1) + r) :=
        RightAgree_not_succ hRag hRag'
      intro hc
      apply hneF
      have h3' : cyc hG S ((a.val + G - ℓ) % G + (ℓ + (L - 1) + r))
          = cyc hG S ((b.val + G - ℓ) % G + (ℓ + (L - 1) + r)) := by
        show Genome.cycl (mkGenome hG S) ((a.val + G - ℓ) % G + (ℓ + (L - 1) + r))
          = Genome.cycl (mkGenome hG S) ((b.val + G - ℓ) % G + (ℓ + (L - 1) + r))
        exact hc
      have h1 : cyc hG S ((a.val + G - ℓ) % G + (ℓ + (L - 1) + r))
          = cyc hG S (a.val + (L - 1) + r) := by
        refine cyc_congr' hG S ?_
        have h2 := Nat.add_mod_eq_add_mod_right (ℓ + (L - 1) + r)
          (Nat.mod_mod (a.val + G - ℓ) G)
        rw [show a.val + G - ℓ + (ℓ + (L - 1) + r) = (a.val + (L - 1) + r) + G
          from by omega, add_G_mod'] at h2
        exact h2
      have h2' : cyc hG S ((b.val + G - ℓ) % G + (ℓ + (L - 1) + r))
          = cyc hG S (b.val + (L - 1) + r) := by
        refine cyc_congr' hG S ?_
        have h2 := Nat.add_mod_eq_add_mod_right (ℓ + (L - 1) + r)
          (Nat.mod_mod (b.val + G - ℓ) G)
        rw [show b.val + G - ℓ + (ℓ + (L - 1) + r) = (b.val + (L - 1) + r) + G
          from by omega, add_G_mod'] at h2
        exact h2
      exact h1.symm.trans (h3'.trans h2')

/-- **A raw repeated `(L-1)`-mer is a branch object**, i.e. the hypothesis of
the bridge really is a branch occurrence of the condensation and nothing
weaker.  This is why the bridge needs no separate `Branch` hypothesis: the
seed already has multiplicity `≥ 2`. -/
theorem Branch_of_vtx_eq_ne {G : ℕ} (hG : 0 < G) {L : ℕ} (S : Fin G → α)
    {a b : Fin G} (hne : a ≠ b) (hvtx : vtx hG L S a = vtx hG L S b) :
    Branch hG L S (vtx hG L S a) := by
  have ha : a ∈ fibre hG L S (vtx hG L S a) :=
    (mem_fibre hG L S (v := vtx hG L S a) (r := a)).mpr rfl
  have hb : b ∈ fibre hG L S (vtx hG L S a) := by
    rw [hvtx]
    exact (mem_fibre hG L S (v := vtx hG L S b) (r := b)).mpr rfl
  have hcard : 2 ≤ (fibre hG L S (vtx hG L S a)).card := by
    have h2 : ({a, b} : Finset (Fin G)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by
        intro hmem
        exact hne (Finset.mem_singleton.mp hmem))]
      simp
    calc 2 = ({a, b} : Finset (Fin G)).card := h2.symm
      _ ≤ (fibre hG L S (vtx hG L S a)).card := by
          apply Finset.card_le_card
          refine Finset.insert_subset ha ?_
          intro b' hb'
          rw [Finset.mem_singleton.mp hb']
          exact hb
  unfold Branch
  rw [← card_fibre hG L S (vtx hG L S a)]
  exact hcard

/-! ## 5. The bridge in obstruction form

The bridge, packaged with the fact that the seed is a branch object of the
condensed `(L-1)`-mer graph, and with the residue condition of the seed made
explicit.  This is the form a step-3 proof would consume: two distinct branch
occurrences of a repeated `(L-1)`-mer of a primitive truth give a maximal
repeat of length `≥ L - 1`. -/

theorem repeated_occurrence_gives_long_maximal_repeat {G : ℕ} (hG : 0 < G) {L : ℕ}
    (hL : 2 ≤ L) (S : Fin G → α) {a b : Fin G} (hne : a ≠ b)
    (hvtx : vtx hG L S a = vtx hG L S b) (hprim : IsPrimitive hG S) :
    (Branch hG L S (vtx hG L S a)) ∧
      (∃ (e : ℕ) (a' b' : Fin G), L - 1 ≤ e ∧ e < G ∧ a' ≠ b' ∧
        (mkGenome hG S).IsRepeat e a' b') :=
  ⟨Branch_of_vtx_eq_ne hG S hne hvtx,
   maximal_extension_of_repeated hG hL S hne hvtx hprim⟩

/-! ## 6. Scope: the residual gap, stated precisely

**Proved here (step 2 of `docs/bbt-eulerian-cycle-89.md` §6).**  A raw
repeated `(L-1)`-mer occurrence of a primitive truth extends to a maximal
repeat of length `≥ L - 1`, with the `e < G` bound contributed by
`not_primitive_of_ge_G_agree`.  Primitivity is used in exactly two places,
both listed in the file header, and both only to keep an extension below a
full turn.

**Not proved here (step 3 of the same §6).**  That a genuinely distinct
Eulerian cycle of the condensed graph supplies *either* a maximal **triple**
repeat of length `≥ L - 1` *or* two **interleaved** maximal repeats both of
length `≥ L - 1`.  That is the combinatorial core of `thm:BBT`, it is the
single remaining input of the exported population theorem, and
`AssemblyP1.BBTEulerian.EulerianCycleObstruction` is still an explicit
hypothesis of `AssemblyP1.PopulationUniqueness` rather than a theorem.  The
bridge above removes one of the three sub-steps listed in §6 of that note; the
other two (condensation bookkeeping, already available as
`BBTSequenceGraph.branchStarts_eq_biUnion` and `choices_only_at_branch`, and
the dichotomy itself) are untouched.

**Not done deliberately.**  `EulerianCycleObstruction` is *not* restated here
with a primitivity hypothesis, even though the extension bound of step 2 needs
one: `docs/bbt-eulerian-cycle-89.md` §6 offers "thread primitivity into
`BBTCompleteSpectrumUniqueness`" as one of two routes, and taking it would
change the statement of an exported input rather than prove it.  The other
route, an extension bound proved from the assumptions already present, is
blocked because `EulerianCycleObstruction` is stated for arbitrary `Ukkonen`
words, and a non-primitive `Ukkonen` word has no maximal repeat of any
length `≥ L - 1` to conclude from (§5 of
`docs/audit-p2-direct-proof-maximal-extension-2026-09-21.md` records the
related obstruction).  The honest statement is therefore the one proved: the
bridge holds for a primitive truth.  Resolving this discrepancy is part of
step 3, not of step 2.
-/

end AssemblyP1.P2RepeatResidual
