import AssemblyP1.BBTEulerian

/-!
# Maximal extension of a branch pair: the `#89` bridge, kernel-checked

`docs/bbt-eulerian-cycle-89.md` §6 isolates the three sub-steps a proof of
`AssemblyP1.BBTEulerian.EulerianCycleObstruction` needs.  Step 1 (the
condensation bookkeeping) is in `AssemblyP1.BBTCondense.lean` §3.  This
module supplies **step 2** at the strength at which it is actually
available on the word layer:

> two distinct occurrences of the same `(L-1)`-mer extend to a *maximal*
> repeat of length `≥ L-1`.

This is the step the maximal-extension audit
(`docs/audit-p2-direct-proof-maximal-extension-2026-09-21.md`) says cannot be
replaced by "a raw branch pair is a maximal repeat", and the instance in §3
below is the kernel-checked reason: a branch pair whose preceding symbols
agree supports **no** maximal repeat at all, at any length, so the
occurrence pair must be *extended backwards* first.  Once it is, the
extension is a genuine maximal repeat of length `≥ L-1`, which is a
constituent of the `def:P1P2` interleaved clause.

Two points in the existing write-up are settled by what is proved here.

* **No primitivity hypothesis is needed for the length bound.**  The audit
  and `docs/bbt-eulerian-cycle-89.md` §6 both record that the maximal
  extension "needs primitivity of the truth to keep the maximal extension
  below `G`".  That is not so: `Genome.IsRepeat` only asks for `e < S.len`,
  and the agreement lengths considered here are capped at `G - 1`, so the
  maximal extension produced below always has `e < G`
  (`exists_maximalRepeat`, `maximalRepeat_of_branch`).  What primitivity
  would exclude is the *unbounded* case, and that case is excluded here by
  a weaker and more local hypothesis: the two preceding symbols must differ
  (`preceding_eq_of_agrees_ge`).
* **The remaining gap is one-sided and now explicit.**
  `maximalRepeat_of_branch` needs `Preceding a ≠ Preceding b` at the two
  *given* branch occurrences.  What is still missing is the
  backward-extension step producing such a pair, and then the dichotomy of
  step 3 (three occurrences of one branch object, or two interleaved pairs
  of extended occurrences).  §3 below is a concrete, kernel-checked
  instance of a branch pair that needs exactly one backward step; §4
  assembles the two disjuncts of the target from the repeats obtained here;
  §5 names the remaining gap as a `Prop`, unproved, for the record.

## What is proved, and what is not

* **Proved (kernel-checked).**  `exists_maximalRepeat` (the maximal
  extension, in the forward direction, with the length bound `e < G`),
  `agrees_mono`, `preceding_eq_of_agrees_ge` (the period alternative),
  `maximalRepeat_of_branch` (the branch-object corollary, i.e. step 2 for
  every branch pair whose preceding symbols differ), and §3's instances.
* **Proved (kernel-checked).**  §3a: the backward half of step 2 ---
  `BackAgrees`, `max_back_agrees` (how far one must step backwards) and
  `preceding_ne_of_max_back` (at a maximal backward step of size `p < G`
  the backward-extended pair has differing preceding symbols, so
  `maximalRepeat_of_branch` applies to it).
* **Proved (kernel-checked).**  `interleaved_disjunct` and `triple_disjunct`:
  the two disjuncts of `AssemblyP1.BBTEulerian.LongObstruction` are
  *assembled* from repeats of length `≥ L-1` obtained in this module, so
  the target of the `#89` dichotomy is reachable from these objects.
* **Not proved.**  The index arithmetic that a backward step of size `p`
  combined with a forward agreement of length `e₀` yields an agreement of
  length `e₀ + p` at the extended pair; this is what is needed to compose
  §3a with §2, and it is stated as such in §3a.  Nor is `EulerianCycleObstruction`
  itself, i.e. the dichotomy (step 3).  `EulerianCycleObstruction` remains
  the single open input of the exported population theorem; no `sorry`, no
  `admit`, no new axiom.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AssemblyP1.BBTEulerian

open SourceFaithfulIs
open OrientedRigidity
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α)

/-! ## 1. Agreement of two occurrences -/

/-- The two occurrences `a`, `b` carry the same symbols at the `e`
positions `a, a+1, …, a+e-1`: the `(L-1)`-mer-level agreement of
`BBTSequenceGraph.vtx`, written at arbitrary length.  This is
`SourceFaithfulIs.Genome.Agree` on the `mkGenome` of the same word. -/
def Agrees (hG : 0 < G) (S : Fin G → α) (e : ℕ) (a b : Fin G) : Prop :=
  ∀ d : Fin e, cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val)

instance (hG : 0 < G) (S : Fin G → α) (e : ℕ) (a b : Fin G) :
    Decidable (Agrees hG S e a b) := by
  unfold Agrees
  infer_instance

/-- **Agreement is the source-faithful `Agree`.** -/
theorem agrees_iff_agree (hG : 0 < G) (S : Fin G → α) (e : ℕ) (a b : Fin G) :
    Agrees hG S e a b ↔ (mkGenome hG S).Agree e a b := Iff.rfl

/-- `Genome.cycl` at the `mkGenome` of the word layer is `cyc`. -/
theorem cycl_mkGenome (hG : 0 < G) (S : Fin G → α) (i : ℕ) :
    (mkGenome hG S).cycl i = cyc hG S i := rfl

/-- The `mkGenome` has the word's length. -/
theorem len_mkGenome (hG : 0 < G) (S : Fin G → α) : (mkGenome hG S).len = G := rfl

/-- **Agreement is downward closed in the length**: a shorter agreement is
a prefix of a longer one. -/
theorem agrees_mono (hG : 0 < G) (S : Fin G → α) {a b : Fin G} {e e' : ℕ} (he' : e' ≤ e)
    (hag : Agrees hG S e a b) : Agrees hG S e' a b := by
  intro d
  have hd : d.val < e := lt_of_lt_of_le d.isLt he'
  exact hag ⟨d.val, hd⟩

/-- **Agreement over a full turn makes the shift a period.**  If `a` and
`b` agree on `G` consecutive positions then the two preceding symbols
coincide, so `(a, b)` is a *periodic* pair: no maximal repeat is available
at these starts at all.  This is the case in which the maximal extension
of §2 is unbounded, and it is why `exists_maximalRepeat` needs the
preceding-symbol hypothesis; no primitivity of the truth is required. -/
theorem preceding_eq_of_agrees_ge {a b : Fin G} {e : ℕ} (hag : Agrees hG S e a b) (he : G ≤ e) :
    (mkGenome hG S).Preceding a = (mkGenome hG S).Preceding b := by
  have h := hag ⟨G - 1, by omega⟩
  have h2 : cyc hG S (a.val + G - 1) = cyc hG S (b.val + G - 1) := by
    rw [Nat.add_sub_assoc (m := G) (k := 1) (by omega) a.val,
      Nat.add_sub_assoc (m := G) (k := 1) (by omega) b.val]
    exact h
  simpa only [SourceFaithfulIs.Genome.Preceding, len_mkGenome, cycl_mkGenome] using h2

/-- **The agreement lengths below `G` of two occurrences**: a downward
closed, nonempty set whose maximum is the maximal extension length. -/
def agreeSet (hG : 0 < G) (S : Fin G → α) (a b : Fin G) : Finset ℕ :=
  (Finset.range G).filter (fun e => Agrees hG S e a b)

/-! ## 2. The maximal extension -/

/-- **The maximal agreement length.**  The set of agreement lengths below
`G` is downward closed and nonempty, so it has a maximum `m`; `m` is an
agreement length, `m ≥ e₀`, `m < G`, and --- whenever `m+1` is still below
`G` --- `m+1` is not an agreement length.  This is the whole content of
"the two occurrences extend to a maximal repeat", isolated from the repeat
predicates.  The caveat on `m+1` is real: agreement at length `≥ G` is
the *periodic* case (`preceding_eq_of_agrees_ge`), in which there is no
maximal repeat at all. -/
theorem max_of_agrees {a b : Fin G} {e₀ : ℕ} (hag0 : Agrees hG S e₀ a b)
    (he₀ : e₀ < G) :
    ∃ m : ℕ, Agrees hG S m a b ∧ e₀ ≤ m ∧ m < G ∧
      (m + 1 < G → ¬ Agrees hG S (m + 1) a b) := by
  have hne : (agreeSet hG S a b).Nonempty :=
    ⟨e₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr he₀, hag0⟩⟩
  have hmem0 : e₀ ∈ agreeSet hG S a b :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr he₀, hag0⟩
  refine ⟨(agreeSet hG S a b).max' hne, ?_, Finset.le_max' _ e₀ hmem0,
    Finset.mem_range.mp (Finset.mem_filter.mp (Finset.max'_mem _ hne)).1, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  · intro hlt h
    have hmem1 : (agreeSet hG S a b).max' hne + 1 ∈ agreeSet hG S a b :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, h⟩
    have hle := Finset.le_max' (agreeSet hG S a b) _ hmem1
    rw [show (agreeSet hG S a b).max' ⟨_, hmem1⟩ = (agreeSet hG S a b).max' hne from rfl] at hle
    omega

/-- **The maximal extension, forward.**  If the two occurrences `a`, `b`
agree on some window of length `e₀` with `1 ≤ e₀ < G` and their *preceding*
symbols differ, then they agree on a window of maximal length `e` with
`e₀ ≤ e < G`, and the symbols following those maximal windows differ as
well: `(a, b)` carries a **maximal repeat** of length `≥ e₀`, and its
length is automatically below `|S|`.

The proof is the classical one: the agreement lengths below `G` form a
downward-closed nonempty set, so it has a maximum `e` (`max_of_agrees`);
maximality forces the two following symbols to differ, and the
preceding-symbol hypothesis is what was needed in the first place.  This is
the "maximal extension" that the `#89` route needs in place of the refuted
"raw node pair is a maximal repeat". -/
theorem exists_maximalRepeat {a b : Fin G} {e₀ : ℕ}
    (hab : a ≠ b) (h1 : 1 ≤ e₀) (he₀ : e₀ < G) (hag : Agrees hG S e₀ a b)
    (hprec : (mkGenome hG S).Preceding a ≠ (mkGenome hG S).Preceding b) :
    ∃ e : Fin G, (mkGenome hG S).IsRepeat e a b ∧ e₀ ≤ e.val := by
  obtain ⟨m, hagm, hge, hmG, hmn⟩ := max_of_agrees (α := α) hG S hag he₀
  -- The two following symbols differ, by maximality of `m`.
  have hfoll : (mkGenome hG S).Following m a
      ≠ (mkGenome hG S).Following m b := by
    intro h
    have h' : cyc hG S (a.val + m) = cyc hG S (b.val + m) := by
      simpa only [SourceFaithfulIs.Genome.Following, cycl_mkGenome] using h
    by_cases hlt : m + 1 < G
    · exact hmn hlt (fun d => by
        by_cases hd : d.val < m
        · exact hagm ⟨d.val, hd⟩
        · rw [Nat.eq_of_lt_succ_of_not_lt d.isLt hd]
          exact h')
    · -- `m = G - 1`, so the two following symbols are the two *preceding*
      -- symbols, which is the hypothesis we started from.
      have hm1 : m = G - 1 := by omega
      rw [hm1] at h'
      have hpe : (mkGenome hG S).Preceding a = (mkGenome hG S).Preceding b := by
        simpa only [SourceFaithfulIs.Genome.Preceding, len_mkGenome, cycl_mkGenome,
          Nat.add_sub_assoc (m := G) (k := 1) (by omega)] using h'
      exact hprec hpe
  have h1m : 1 ≤ m := Nat.le_trans h1 hge
  exact ⟨⟨m, hmG⟩, ⟨h1m, hmG, hab, hagm, hprec, hfoll⟩, hge⟩

/-- **The maximal extension at two occurrences of a branch object.**  This
is step 2 of the `#89` roadmap at the strength available on the word
layer: two distinct starts carrying the same `(L-1)`-mer, whose *preceding*
symbols differ, yield a maximal repeat of length `≥ L-1` --- a constituent
of the interleaved clause of `def:P1P2`, read at the threshold `K = L-1` of
`thm:BBT`.

The case `L-1 ≥ G` is discharged first: agreement over a full turn of the
circle makes the shift a period, so the two preceding symbols agree and the
hypothesis is contradictory.  This is what keeps the produced length below
`|S|`, with no primitivity assumption on the truth. -/
theorem maximalRepeat_of_branch {L : ℕ} (hL : 2 ≤ L) {a b : Fin G}
    (hab : a ≠ b) (hvt : vtx hG L S a = vtx hG L S b)
    (hprec : (mkGenome hG S).Preceding a ≠ (mkGenome hG S).Preceding b) :
    ∃ e : Fin G, (mkGenome hG S).IsRepeat e a b ∧ L - 1 ≤ e.val := by
  have hK1 : 1 ≤ L - 1 := by omega
  have hag : Agrees hG S (L - 1) a b := fun d => congrFun hvt d
  by_cases hle : L - 1 < G
  · obtain ⟨e, he, hlen⟩ :=
      exists_maximalRepeat (α := α) hG S hab hK1 hle hag hprec
    exact ⟨e, he, hlen⟩
  · exact absurd (preceding_eq_of_agrees_ge (α := α) hG S hag (by omega)) hprec

/-- ... read at a branch vertex: two distinct realisations of one branch
object, with different preceding symbols, are a maximal repeat of length
`≥ L-1`.  This is the version the dichotomy would consume, since the
occurrences it produces are the fibres of one condensed vertex
(`BBTSequenceGraph.branchVerts`, `BBTSequenceGraph.fibre`). -/
theorem maximalRepeat_of_branchVertex {L : ℕ} (hL : 2 ≤ L)
    {v : Fin (L - 1) → α} (hbr : Branch hG L S v)
    (hprec : ∀ x y : Fin G, vtx hG L S x = v → vtx hG L S y = v → x ≠ y →
      (mkGenome hG S).Preceding x ≠ (mkGenome hG S).Preceding y) :
    ∃ a b e : Fin G, a ≠ b ∧ vtx hG L S a = vtx hG L S b ∧
      (mkGenome hG S).IsRepeat e a b ∧ L - 1 ≤ e.val := by
  have h2 : 2 ≤ (fibre hG L S v).card := by rw [card_fibre]; exact hbr
  obtain ⟨a, b, ha, hb, hab⟩ := two_of_card_ge_two (s := fibre hG L S v) h2
  have hva : vtx hG L S a = v :=
    (mem_fibre (hG := hG) (L := L) (S := S) (v := v) (r := a)).mp ha
  have hvb : vtx hG L S b = v :=
    (mem_fibre (hG := hG) (L := L) (S := S) (v := v) (r := b)).mp hb
  have hvt' : vtx hG L S a = vtx hG L S b := hva.trans hvb.symm
  obtain ⟨e, he, hlen⟩ :=
    maximalRepeat_of_branch (α := α) hG S hL hab hvt' (hprec a b hva hvb hab)
  exact ⟨a, b, e, hab, hvt', he, hlen⟩

/-! ## 3. Kernel-checked instances -/

section Instances

/-- `S = 0111` at `G = 4`, `L = 2` (so the vertices of the `(L-1)`-mer
multigraph are single symbols). -/
def S0111 : Fin 4 → Fin 2 := ![0, 1, 1, 1]

theorem hG4b : 0 < 4 := by decide

/-- The symbol `1` is a **branch object** of the condensation: it occurs
three times. -/
theorem branch_0111 : Branch hG4b 2 S0111 (![1]) := by decide

/-- ... realised at the two starts `2` and `3`. -/
theorem branchPair_0111 :
    vtx hG4b 2 S0111 (2 : Fin 4) = ![(1)] ∧ vtx hG4b 2 S0111 (3 : Fin 4) = ![(1)] := by
  decide

/-- The two starts `2`, `3` have *equal* preceding symbols, so they cannot
carry a maximal repeat: the hypothesis of `maximalRepeat_of_branch` is
genuinely needed. -/
theorem preceding_eq_branchPair_0111 :
    (mkGenome hG4b S0111).Preceding (2 : Fin 4)
      = (mkGenome hG4b S0111).Preceding (3 : Fin 4) := by
  decide

/-- **A branch pair need not carry a maximal repeat at its own starts.**
The starts `2`, `3` realise the same branch object and have *equal*
preceding symbols, so they support no maximal repeat at any length below
`|S|`: `Genome.IsRepeat` requires the preceding symbols to differ.  This
is the kernel-checked reason the `#89` route must extend occurrences
backwards before it may speak of maximal repeats, and it is the
`Preceding a ≠ Preceding b` hypothesis of `maximalRepeat_of_branch` doing
real work. -/
theorem not_maximalRepeat_branchPair_0111 :
    ¬ ∃ e : Fin 4, (mkGenome hG4b S0111).IsRepeat e ((2 : Fin 4)) ((3 : Fin 4)) := by
  rintro ⟨e, he⟩
  have hne : (mkGenome hG4b S0111).Preceding (2 : Fin 4)
      ≠ (mkGenome hG4b S0111).Preceding (3 : Fin 4) := he.2.2.2.2.1
  exact hne (Eq.trans preceding_eq_branchPair_0111.symm rfl)

/-- **One backward step suffices here**, and the extended pair is exactly
what `maximalRepeat_of_branch` produces.  The starts `1`, `2` --- the pair
obtained by stepping the branch pair `2`, `3` one position backwards ---
have different preceding symbols and support the maximal repeat of length
`2 ≥ L-1 = 1`.  So the extended branch pair is a constituent of the
interleaved clause, and it is kernel-checked that it is one. -/
theorem maximalRepeat_of_branch_0111 :
    ∃ e : Fin 4, (mkGenome hG4b S0111).IsRepeat e ((1 : Fin 4)) ((2 : Fin 4)) ∧
      (2 - 1 : ℕ) ≤ e.val := by
  have hab : (1 : Fin 4) ≠ 2 := by decide
  have hvt' : vtx hG4b 2 S0111 (1 : Fin 4) = vtx hG4b 2 S0111 (2 : Fin 4) := by decide
  have hprec : (mkGenome hG4b S0111).Preceding (1 : Fin 4)
      ≠ (mkGenome hG4b S0111).Preceding (2 : Fin 4) := by decide
  have hL2 : (2 : ℕ) ≤ 2 := by decide
  exact maximalRepeat_of_branch (L := 2) (α := Fin 2) hG4b S0111 hL2 hab hvt' hprec

/-- ... witnessed by the preceding-symbol difference. -/
theorem preceding_ne_branchPairStep_0111 :
    (mkGenome hG4b S0111).Preceding (1 : Fin 4)
      ≠ (mkGenome hG4b S0111).Preceding (2 : Fin 4) := by
  decide

theorem maximalRepeat_of_extendedBranchPair_0111 :
    ∃ e : Fin 4, (mkGenome hG4b S0111).IsRepeat e ((1 : Fin 4)) ((2 : Fin 4)) ∧
      (mkGenome hG4b S0111).Preceding (1 : Fin 4)
        ≠ (mkGenome hG4b S0111).Preceding (2 : Fin 4) := by
  obtain ⟨e, he, hlen⟩ := maximalRepeat_of_branch_0111
  exact ⟨e, he, preceding_ne_branchPairStep_0111⟩

end Instances

/-! ## 3a. Stepping backwards: the other half of step 2

`maximalRepeat_of_branch` (step 2, forward) needs two occurrences of one
`(L-1)`-mer whose *preceding* symbols differ, and §3 above shows a branch
pair need not have that.  This section is the backward half of the step:
how far one has to step backwards before the preceding symbols differ, and
why the stepping cannot go on forever.

`BackAgrees p a b` says the two occurrences `a`, `b` agree at the `p`
positions immediately *preceding* them.  It is downward closed in `p` and
contains `0`, so it has a maximum `p ≤ G` (`max_back_agrees`), and at a
maximal `p < G` the preceding symbols differ
(`preceding_ne_of_max_back`).  The excluded case `p = G` is exactly the
periodic case: the two occurrences have been seen at *every* position of
the circle, so the shift from one to the other is a period, which is
`preceding_eq_of_agrees_ge`'s alternative for the forward direction.

The arithmetic that combines a backward step of `p` with a forward
agreement of length `e₀` into an agreement of length `e₀ + p` is **not**
carried out here; see the docstring of the module. -/

/-- **The two occurrences agree at the `p` positions immediately
preceding them**: stepping backwards from `a` and from `b` by the same
number of positions gives the same symbols.  This is the backward analogue
of `Agrees`, at the level of positions; `p = 0` is the trivial agreement
and `p = 1` says the two preceding symbols agree. -/
def BackAgrees (hG : 0 < G) (S : Fin G → α) (a b : Fin G) (p : ℕ) : Prop :=
  ∀ d : Fin p, cyc hG S (prevPos hG ((prevPos hG)^[d.val] a)).val
    = cyc hG S (prevPos hG ((prevPos hG)^[d.val] b)).val

instance (hG : 0 < G) (S : Fin G → α) (a b : Fin G) (p : ℕ) :
    Decidable (BackAgrees hG S a b p) := by
  unfold BackAgrees
  infer_instance

/-- **The backward agreement lengths of two occurrences**: a set
containing `0`, whose maximum is the number of positions one has to step
backwards before the preceding symbols differ. -/
def backAgreeSet (hG : 0 < G) (S : Fin G → α) (a b : Fin G) : Finset ℕ :=
  (Finset.range (G + 1)).filter (fun p => BackAgrees hG S a b p)

/-- Cyclic access ignores a further turn of the circle. -/
theorem cyc_mod (hG : 0 < G) (S : Fin G → α) (i : ℕ) : cyc hG S i = cyc hG S (i % G) := by
  simp [cyc]

/-- The preceding symbol of `x` is the symbol at the previous position. -/
theorem preceding_eq_prevPos (hG : 0 < G) (S : Fin G → α) (x : Fin G) :
    (mkGenome hG S).Preceding x = cyc hG S (prevPos hG x).val := by
  simp only [SourceFaithfulIs.Genome.Preceding, len_mkGenome, cycl_mkGenome, prevPos]
  exact cyc_mod hG S _

/-- **The maximal backward agreement.**  The `p` at which two occurrences
agree on the `p` positions before them contain `0`, so they have a maximum
`p ≤ G`; and if `p < G` the agreement stops at `p`.  `p = G` is the
periodic case: the two occurrences coincide with each other at every
position of the circle, and `preceding_eq_of_agrees_ge` is the forward
analogue of that exclusion. -/
theorem max_back_agrees (a b : Fin G) :
    ∃ p : ℕ, p ≤ G ∧ BackAgrees hG S a b p ∧
      (p < G → ¬ BackAgrees hG S a b (p + 1)) := by
  have hzero : 0 ∈ backAgreeSet hG S a b := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _), ?_⟩
    intro d
    exact Fin.elim0 d
  have hne : (backAgreeSet hG S a b).Nonempty := ⟨0, hzero⟩
  have hle : (backAgreeSet hG S a b).max' hne ≤ G := by
    have hlt := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.max'_mem _ hne)).1
    omega
  have hagp : BackAgrees hG S a b ((backAgreeSet hG S a b).max' hne) :=
    (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  refine ⟨(backAgreeSet hG S a b).max' hne, hle, hagp, ?_⟩
  intro hp h
  have hmem' : (backAgreeSet hG S a b).max' hne + 1 ∈ backAgreeSet hG S a b :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩
  have hle' := Finset.le_max' (backAgreeSet hG S a b) _ hmem'
  rw [show (backAgreeSet hG S a b).max' ⟨_, hmem'⟩
      = ((backAgreeSet hG S a b).max' hne) from rfl] at hle'
  omega

/-- **Stepping backwards, the preceding symbols eventually differ.**  If
`p < G` is a maximal backward agreement of `a`, `b`, then the occurrences
one step *before* the backward-extended pair `prevPos^[p] a`,
`prevPos^[p] b` have different preceding symbols, i.e. that pair is a
pair to which `maximalRepeat_of_branch` applies.  This is the
backward-extension step of the `#89` route, isolated from the index
arithmetic that would also have to show the extended pair still agrees
forward. -/
theorem preceding_ne_of_max_back (a b : Fin G) {p : ℕ} (hp : p < G)
    (hagp : BackAgrees hG S a b p) (hnot : ¬ BackAgrees hG S a b (p + 1)) :
    (mkGenome hG S).Preceding ((prevPos hG)^[p] a)
      ≠ (mkGenome hG S).Preceding ((prevPos hG)^[p] b) := by
  unfold BackAgrees at hnot
  rw [not_forall] at hnot
  obtain ⟨d, hd⟩ := hnot
  have hdp : d.val = p := by
    by_contra hc
    have hlt : d.val < p := by omega
    exact hd (hagp ⟨d.val, hlt⟩)
  have hd' : ¬ (cyc hG S (prevPos hG ((prevPos hG)^[p] a)).val
      = cyc hG S (prevPos hG ((prevPos hG)^[p] b)).val) := by
    intro hz
    have hdEq : d = ⟨p, by omega⟩ := Fin.ext hdp
    rw [hdEq] at hd
    exact hd hz
  intro h
  rw [preceding_eq_prevPos hG S, preceding_eq_prevPos hG S] at h
  exact hd' h

/-! ## 4. Assembling the two disjuncts of `LongObstruction` -/

/-- **The second disjunct of `LongObstruction` from two extended branch
pairs.**  Two maximal repeats of length `≥ L-1` whose four starts
interleave are exactly the interleaved clause of `def:P1P2` at the
threshold `K = L-1`, i.e. one of the two ways in which the `Ukkonen`
hypothesis of `thm:BBT` can fail.  This is the target that step 3 of the
`#89` roadmap has to hit, packaged so that the two maximal repeats can be
supplied by `maximalRepeat_of_branch`. -/
theorem interleaved_disjunct {L : ℕ} {e₁ e₂ a b c d : Fin G}
    (h₁ : (mkGenome hG S).IsRepeat e₁ a b) (h₂ : (mkGenome hG S).IsRepeat e₂ c d)
    (hi : Interleaved (mkGenome hG S) a b c d)
    (h1 : L - 1 ≤ e₁.val) (h2 : L - 1 ≤ e₂.val) :
    LongObstruction hG L S :=
  Or.inr ⟨e₁, e₂, a, b, c, d, h₁, h₂, hi, h1, h2⟩

/-- **The first disjunct of `LongObstruction`.**  Three selected
occurrences carrying a maximal triple repeat of length `≥ L-1` are the
other way in which `Ukkonen` can fail; it is recorded here so that both
disjuncts of the `#89` dichotomy are named in one place. -/
theorem triple_disjunct {L : ℕ} {e a b c : Fin G}
    (ht : (mkGenome hG S).IsTripleRepeat e a b c) (hlen : L - 1 ≤ e.val) :
    LongObstruction hG L S :=
  Or.inl ⟨e, a, b, c, ht, hlen⟩

/-! ## 5. The remaining gap, stated and left open

Two occurrences of a branch object whose preceding symbols agree are the
obstruction to step 2 as proved above, and step 3 --- the dichotomy itself
--- is not attempted.  `EulerianCycleGap` names the statement that would
close the `#89` route; it is a `Prop`, it is **not** an inhabitant, and
nothing in the library depends on it. -/

/-- **The remaining gap of the `#89` route**, as a `Prop` with no
inhabitant: every alternative Eulerian cycle of the condensed `(L-1)`-mer
multigraph of an `Ukkonen` word has the truth's own vertex cycle.  This is
step 2 (together with the backward extension) plus step 3 of
`docs/bbt-eulerian-cycle-89.md` §6, i.e. the uniqueness half of
`EulerianCycleObstruction`.  It is **not** proved; see the module
docstring. -/
def EulerianCycleGap {L : ℕ} : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), Ukkonen hK L S →
    ∀ (σ : Fin K ≃ Fin K), EulerianCycle hK L S σ →
      VertexCycleEq hK L S σ (Equiv.refl (α := Fin K))

end AssemblyP1.BBTEulerian
