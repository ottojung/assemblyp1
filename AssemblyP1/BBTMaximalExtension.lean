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
* **The remaining gap is now one-sided and explicit.**  Step 2 --- turning a
  branch pair into a maximal repeat of length `≥ L-1` --- is proved in full
  for a **primitive** truth, at *arbitrary* starts
  (`maximalRepeat_of_branch_backward`): the two occurrences are moved back
  together by the *maximal backward step* `p`, at which the two preceding
  symbols differ and the extended pair still spells the same `(L-1)`-mer.
  What is still missing is the dichotomy of step 3 (three occurrences of one
  branch object, or two interleaved pairs of extended occurrences).  §3
  below is a concrete, kernel-checked instance of a branch pair that needs
  a backward step; §4 assembles the two disjuncts of the target from the
  repeats obtained here; §5 names the remaining gap as a `Prop`, unproved,
  for the record.

## What is proved, and what is not

* **Proved (kernel-checked).**  `exists_maximalRepeat` (the maximal
  extension, in the forward direction, with the length bound `e < G`),
  `agrees_mono`, `preceding_eq_of_agrees_ge` (the period alternative),
  `maximalRepeat_of_branch` (the branch-object corollary, i.e. step 2 for
  every branch pair whose preceding symbols differ), and §3's instances.
* **Proved (kernel-checked).**  §3a: the backward half of step 2 ---
  `BackAgrees`, `max_back_agrees` (how far one must step backwards) and
  `preceding_ne_of_max_back` (at a maximal backward step of size `p < G`
  the pair `prevPos^[p] a`, `prevPos^[p] b` has differing preceding symbols,
  so `maximalRepeat_of_branch` applies to it).
* **Proved (kernel-checked).**  §4a: the whole index arithmetic of the
  backward step.  `agrees_of_backAgrees` composes a forward agreement of
  length `e₀` at `(a, b)` with a backward agreement of size `p` into an
  agreement of length `e₀ + p` at `(prevPos^[p] a, prevPos^[p] b)`, at the
  residue level (`BackAgreesE`, `backResidue`, `backResidue_step`) with no
  off-by-one: `BackAgrees p` covers the positions `a-1, …, a-p`, so the
  composition needs exactly `BackAgrees p` and the maximal step supplies it.
* **Proved (kernel-checked).**  §4a.3: the **full-period case is excluded,
  rigorously, and primitively**.  `not_primitive_of_backAgrees_G` turns a
  backward agreement over a full turn at two distinct starts into
  shift-invariance, i.e. non-primitivity
  (`RepeatAdapter.not_primitive_of_ge_G_agree`); `exists_backStep_lt_G`
  concludes `p < G` from primitivity.  This is the only place in the module
  where primitivity is used, and it is used for no other purpose: the
  maximal extension of §2 needs no primitivity, because the length it
  produces is bounded by `|S|` by construction (§2).
* **Proved (kernel-checked).**  `maximalRepeat_of_branch_backward`: for a
  primitive truth, two distinct occurrences of one `(L-1)`-mer, at
  *arbitrary* starts, extend to a maximal repeat of length `≥ L-1` whose two
  starts are the two occurrences moved back together by the same maximal
  backward amount.  The theorem the `#89` route consumes: minimal
  hypotheses (`2 ≤ L`, `a ≠ b`, equal `(L-1)`-mers, primitivity), no
  `Preceding a ≠ Preceding b`, and a length bound that follows from
  primitivity rather than being assumed.
* **Proved (kernel-checked).**  §4a.4: the backward step is a *rotation* of
  the circle, hence preserves cyclic order: `openArc_backward` (three
  occurrences lie in the open arc from `a` to `b` iff they do after all
  three are stepped back by `p`) and `interleaved_backward` (likewise for
  `Interleaved`, at a common step count).  This is the cyclic-order
  relationship between a branch pair and the maximal repeat built out of
  it.  Its docstring also records the one thing it does *not* give: at two
  *different* step counts the shifted starts can collide
  (`prevPos^[1] 1 = prevPos^[2] 2` on the circle), so the dichotomy must take
  the interleaving of the two maximal repeats' starts as a hypothesis ---
  which is exactly what `LongObstruction`'s second disjunct does --- and
  cannot deduce it from the interleaving of the two occurrence pairs.
* **Proved (kernel-checked).**  §4a.6: `S0111_primitive` and
  `maximalRepeat_branch_backward_0111`, an end-to-end instance of the whole
  route on the word `0111` of §3.
* **Proved (kernel-checked).**  `interleaved_disjunct` and `triple_disjunct`:
  the two disjuncts of `AssemblyP1.BBTEulerian.LongObstruction` are
  *assembled* from repeats of length `≥ L-1` obtained in this module, so
  the target of the `#89` dichotomy is reachable from these objects.
* **Not proved.**  `EulerianCycleObstruction` itself, i.e. the dichotomy
  (step 3): that a branch vertex of the condensed `(L-1)`-mer multigraph
  carries either three occurrences spelling a maximal triple repeat, or two
  pairs of occurrences of *different* branch objects whose extended maximal
  repeats interleave.  Step 2, including the periodic case, is no longer
  part of the gap.  `EulerianCycleObstruction` remains the single open input
  of the exported population theorem; no `sorry`, no `admit`, no new axiom.
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
theorem preceding_eq_of_agrees_ge {a b : Fin G} {e : ℕ}
    (hag : Agrees hG S e a b) (he : G ≤ e) :
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
agreement of length `e₀` into an agreement of length `e₀ + p` is carried out
in §4a below (`agrees_of_backAgrees`), together with the exclusion of the
periodic case `p = G` (§4a.3). -/

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
`prevPos^[p] a`, `prevPos^[p] b` have different *preceding* symbols, so that
pair is a pair to which `maximalRepeat_of_branch` applies.

The indexing is worth spelling out.  `BackAgrees p` covers the indices
`0, …, p-1`, i.e. the positions `a-1, a-2, …, a-p`; the failing index of
`¬ BackAgrees (p+1)` is `p`, i.e. the position `a-p-1`.  The *preceding*
symbol of `prevPos^[p] a` is the symbol at `a-p-1`, so the shift is `p` and
the same `p` that §4a.2 shifts by. -/
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
  have hdEq : d = ⟨p, by omega⟩ := Fin.ext hdp
  rw [hdEq] at hd
  intro h
  rw [preceding_eq_prevPos hG S, preceding_eq_prevPos hG S] at h
  exact hd h

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

/-! ## 4a. The index arithmetic: composing a backward step with a forward agreement

This section carries out the index arithmetic of the `#89` route, and it is
where the forward and backward halves of step 2 are joined.

The point of the composition is this.  Write `δ` for the shift from the
first occurrence to the second.  `Agrees e₀ a b` says the word is
`δ`-invariant on the arc `[a, a + e₀)`, and `BackAgrees p a b` says it is
`δ`-invariant on the arc `[a - p, a)`.  The two arcs share no position and
together form the arc `[a - p, a + e₀)`, of length `e₀ + p`; that arc is
exactly the length-`e₀ + p` window of the *backward-shifted* pair
`prevPos^[p] a`, `prevPos^[p] b`.  So

  `Agrees e₀ a b → BackAgrees p a b → Agrees (e₀ + p) (prevPos^[p] a) (prevPos^[p] b)`

which is `agrees_of_backAgrees` below.  Taking `e₀ = L - 1`, the
backward-extended branch pair spells the same `(L-1)`-mer *and* has been
extended backwards by `p` symbols: this is the correct long maximal repeat
of the pair --- not the raw pair (which may carry no maximal repeat at all,
§3) and not the pair at the given starts, but the pair read at the maximal
backward step.

The indexing is the delicate part, and it is worth being explicit about it.
`BackAgrees p a b` covers the indices `0, …, p-1` of
`prevPos ∘ (prevPos^[·])`, i.e. the positions `a-1, a-2, …, a-p`; so
`p = 1` says the two *preceding* symbols agree, and the position `a - p` ---
the first position of the composed arc --- is the *last* index covered.  The
failing index of `¬ BackAgrees (p+1) a b` is `p`, i.e. the position
`a - p - 1`, which is the preceding symbol of `prevPos^[p] a`.  Both facts
are used verbatim: the composition consumes `BackAgrees p` and the
preceding-symbol difference comes from the *same* `p`, so that the pair the
maximal repeat is built at is exactly the pair whose window the composition
produced.

The excluded case is the periodic one, and it is handled by primitivity and
by nothing else (§4a.3): a backward agreement of a *full turn* makes the
shift `δ` a period of the word, so for a primitive word it forces
`a = b`.  Hence at two distinct occurrences the maximal backward step is
strictly below `G`, and `prevPos^[p] a` is a well-formed start distinct from
`prevPos^[p] b`. -/

/-! ### 4a.1 Residue arithmetic for one backward step -/

/-- `cyc` depends only on its argument modulo `G`.  (A local copy of the
`private` helper `AssemblyP1.RepeatAdapter.cyc_congr`; `cyc_mod` in §3a is
the `+ G` special case and is not enough here.) -/
theorem cyc_congr' (hG : 0 < G) (S : Fin G → α) {x y : ℕ}
    (h : x % G = y % G) : cyc hG S x = cyc hG S y := by
  unfold cyc
  exact congrArg S (Fin.ext h)

/-- `cyc` at `n` equals `cyc` at `n % G`. -/
theorem cyc_mod' (hG : 0 < G) (S : Fin G → α) (n : ℕ) : cyc hG S n = cyc hG S (n % G) :=
  cyc_congr' hG S (Nat.mod_mod n G).symm

/-- **Modulus cancellation below `G`**: two numbers in `[0, G)` with equal
residues are equal. -/
theorem mod_inj_of_lt (hG : 0 < G) {x y : ℕ} (hx : x < G) (hy : y < G)
    (h : x % G = y % G) : x = y := by
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
  exact h

/-- **Modulus cancellation on `[1, G]`**: two numbers in `[1, G]` with equal
residues are equal.  The `0 < ·` hypotheses are needed precisely to separate
the pair `0, G`, which shares a residue. -/
theorem mod_inj_of_le' (hG : 0 < G) {x y : ℕ} (hx : 0 < x) (hx' : x ≤ G)
    (hy : 0 < y) (hy' : y ≤ G) (h : x % G = y % G) : x = y := by
  by_cases hxG : x = G
  · by_cases hyG : y = G
    · omega
    · have hy0 : y % G = y := Nat.mod_eq_of_lt (by omega)
      rw [hxG, Nat.mod_self, hy0] at h
      omega
  · by_cases hyG : y = G
    · have hx0 : x % G = x := Nat.mod_eq_of_lt (by omega)
      rw [hx0, hyG, Nat.mod_self] at h
      omega
    · exact mod_inj_of_lt hG (by omega) (by omega) h

/-- Adding `G` does not change the residue. -/
theorem mod_add_self (hG : 0 < G) (n : ℕ) : (n + G) % G = n % G := by
  simp

/-- **A congruence of residues gives a congruence of `cyc`.** -/
theorem cyc_congr_modEq (hG : 0 < G) (S : Fin G → α) {x y : ℕ} (h : Nat.ModEq G x y) :
    cyc hG S (x % G) = cyc hG S (y % G) := congrArg (cyc hG S) h

/-- Adding a positive number and subtracting `1` again is adding that number
minus `1`; stated because the truncated-subtraction rearrangement it is used
for is not something `omega` performs. -/
theorem add_sub_one (a b : ℕ) (h : 0 < b) : a + (b - 1) = a + b - 1 := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  have e : 0 + 1 + c - 1 = c := by omega
  rw [e]
  have e2 : a + (0 + 1 + c) - 1 = a + c := by omega
  rw [e2]

/-- **One backward step, in residue form.**  Stepping backwards from `v` and
taking the residue agrees with stepping backwards from `v % G`. -/
theorem mod_prev_step (hG : 0 < G) (v : ℕ) :
    ((v % G) + G - 1) % G = (v + G - 1) % G := by
  have h : Nat.ModEq G (v % G) v := Nat.mod_mod v G
  calc ((v % G) + G - 1) % G = (v % G + (G - 1)) % G := by
        have e := add_sub_one (v % G) G hG
        rw [e]
    _ = (v + (G - 1)) % G := h.add_right (G - 1)
    _ = (v + G - 1) % G := by
        have e := (add_sub_one v G hG).symm
        rw [e]

/-- **`d` backward steps from `x` land at residue `x.val + G - d`**, for
`d ≤ G`.  This is the only place the `Fin` index arithmetic of the
composition enters; the nonneg form `x.val + G - d` is why the bound
`d ≤ G` is needed. -/
theorem backResidue (hG : 0 < G) (d : ℕ) (x : Fin G) (hd : d ≤ G) :
    (prevPos hG)^[d] x = ⟨(x.val + G - d) % G, Nat.mod_lt _ hG⟩ := by
  induction d with
  | zero =>
      have e1 : (prevPos hG)^[0] x = x := Function.iterate_zero_apply (f := prevPos hG) x
      apply Fin.ext
      rw [e1]
      have e : (x.val + G - 0) % G = x.val := by
        rw [show x.val + G - 0 = x.val + G by omega, mod_add_self hG]
        exact Nat.mod_eq_of_lt (a := x.val) (b := G) x.isLt
      exact e.symm
  | succ d ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      apply Fin.ext
      simp only [prevPos]
      have h1 := mod_prev_step hG (x.val + G - d)
      have h2 : x.val + G - d + G - 1 = (x.val + G - (d + 1)) + G := by omega
      rw [h1, h2, Nat.add_mod_right]

/-- **One backward step is injective**: `prevPos` is a permutation of the
circle, being the translation by `-1`. -/
theorem prevPos_injective (hG : 0 < G) : Function.Injective (prevPos hG) := by
  intro x y h
  have h1 := congrArg Fin.val h
  simp only [prevPos] at h1
  -- a difference of two numbers of `[0, G)` that is a multiple of `G` vanishes
  have key : ∀ u v : ℕ, u - v < G → G ∣ u - v → u - v = 0 := by
    intro u v hlt hd
    have hz : (u - v) % G = 0 := Nat.mod_eq_zero_of_dvd hd
    rw [Nat.mod_eq_of_lt hlt] at hz
    exact hz
  have hdvd : G ∣ (y.val + G - 1) - (x.val + G - 1) := Nat.ModEq.dvd' h1
  have h0 := key (y.val + G - 1) (x.val + G - 1) (by omega) hdvd
  have hdvd' : G ∣ (x.val + G - 1) - (y.val + G - 1) := Nat.ModEq.dvd' h1.symm
  have h0' := key (x.val + G - 1) (y.val + G - 1) (by omega) hdvd'
  apply Fin.ext
  have hle : x.val + G - 1 ≤ y.val + G - 1 := Nat.sub_eq_zero_iff_le.mp h0'
  have hle' : y.val + G - 1 ≤ x.val + G - 1 := Nat.sub_eq_zero_iff_le.mp h0
  omega

/-- **Backwards iteration is injective**, being an iterate of an injective
map. -/
theorem prevIter_injective (hG : 0 < G) (p : ℕ) :
    Function.Injective ((prevPos hG)^[p]) := by
  induction p with
  | zero => intro x y h; exact h
  | succ p ih =>
      intro x y h
      have h' : (prevPos hG)^[p] (prevPos hG x) = (prevPos hG)^[p] (prevPos hG y) := by
        simpa [Function.iterate_succ_apply, Function.comp_def] using h
      exact prevPos_injective hG (ih h')

/-- **Backwards iteration is injective**, so the two backward-shifted
occurrences of a branch pair are two distinct starts. -/
theorem prevIter_ne {a b : Fin G} {p : ℕ} (hp : p ≤ G) (hab : a ≠ b) :
    (prevPos hG)^[p] a ≠ (prevPos hG)^[p] b := by
  intro h
  apply hab
  exact prevIter_injective hG p h

/-- **`cyc` ignores a full turn.** -/
theorem cyc_add_G (hG : 0 < G) (S : Fin G → α) (n : ℕ) : cyc hG S (n + G) = cyc hG S n := by
  have e : (n + G) % G = n % G := by simp
  rw [cyc_mod' hG S, e, (cyc_mod' hG S _).symm]

/-- **Reducing the index modulo `G` inside `cyc`**: for a start `x` and any
offset, the two positions differ by a multiple of `G`. -/
theorem cyc_add (hG : 0 < G) (S : Fin G → α) (x : Fin G) (j : ℕ) :
    cyc hG S (x.val + j) = cyc hG S (x.val + j % G) := by
  calc cyc hG S (x.val + j) = cyc hG S ((x.val + j) % G) := cyc_mod' hG S _
    _ = cyc hG S (x.val + j % G) := by
        have e : (x.val + j) % G = (x.val + j % G) % G := by
          rw [Nat.add_mod, Nat.mod_eq_of_lt (a := x.val) (b := G) x.isLt]
        rw [e]
        exact (cyc_mod' hG S _).symm

/-- The form of `cyc_add` that reads the residue of a *sum*; the composition
below always knows the residue of a single start. -/
theorem cyc_add_mod (hG : 0 < G) (S : Fin G → α) (x : Fin G) (j : ℕ) :
    cyc hG S (x.val + j % G) = cyc hG S ((x.val + j) % G) :=
  (cyc_add hG S x j).symm.trans (cyc_mod' hG S _)

/-! ### 4a.2 The backward agreement in residue form, and the composition -/

/-- **Backward agreement, reindexed as an arc.**  `BackAgreesE p a b` says
the word is invariant under the shift `a ↦ b` at the `p` positions
`a-1, a-2, …, a-p`, i.e. on the arc of `p` positions immediately *preceding*
`a`.  This is the form in which the backward agreement composes with a
forward one, and it is the form in which the `Fin` index arithmetic of §4a.1
applies. -/
def BackAgreesE (hG : 0 < G) (S : Fin G → α) (a b : Fin G) (p : ℕ) : Prop :=
  ∀ j : ℕ, j < p → cyc hG S (a.val + G - 1 - j) = cyc hG S (b.val + G - 1 - j)

/-- **The residue form of one backward step**: stepping `j` times backwards
and then once more lands at residue `x.val + G - 1 - j`.  This is
`backResidue` at `j + 1`, and the bound `j + 1 ≤ G` is why the iff below
needs `p ≤ G`. -/
theorem backResidue_step (hG : 0 < G) (j : ℕ) (x : Fin G) (hj : j + 1 ≤ G) :
    (prevPos hG ((prevPos hG)^[j] x)).val = (x.val + G - 1 - j) % G := by
  have heq : (prevPos hG)^[j + 1] x = prevPos hG ((prevPos hG)^[j] x) := by
    have h2 : (prevPos hG)^[1 + j] x = prevPos hG ((prevPos hG)^[j] x) :=
      Function.iterate_add_apply _ _ _ _
    rw [show 1 + j = j + 1 from by omega] at h2
    exact h2
  rw [← heq, backResidue hG (j + 1) x hj]
  have hx : x.val + G - (j + 1) = x.val + G - 1 - j := by omega
  simp only
  exact congrArg (fun t : ℕ => t % G) hx

/-- **The `cyc`-form of one backward step.** -/
theorem cyc_back_step (hG : 0 < G) (S : Fin G → α) {x : Fin G} {j : ℕ} (hj : j + 1 ≤ G) :
    cyc hG S (prevPos hG ((prevPos hG)^[j] x)).val
      = cyc hG S (x.val + G - 1 - j) := by
  rw [backResidue_step hG j x hj]
  exact (cyc_mod' hG S _).symm

/-- **Backward agreement is the arc statement, for `p ≤ G`.**  This is the
identification of the `prevPos`-iteration definition of §3a with the
residue form; it is the only hypothesis of the composition besides the two
agreements themselves. -/
theorem backAgrees_iff_backAgreesE (hG : 0 < G) (S : Fin G → α) (a b : Fin G) (p : ℕ)
    (hp : p ≤ G) : BackAgrees hG S a b p ↔ BackAgreesE hG S a b p := by
  constructor
  · intro h j hj
    have hj' : j + 1 ≤ G := by omega
    have he := h ⟨j, by omega⟩
    rw [cyc_back_step hG S (x := a) (j := j) hj', cyc_back_step hG S (x := b) (j := j) hj'] at he
    exact he
  · intro h d
    have hd := d.isLt
    have hd' : d.val + 1 ≤ G := by omega
    have he := h d.val (by omega)
    rw [cyc_back_step hG S (x := a) (j := d.val) hd',
      cyc_back_step hG S (x := b) (j := d.val) hd']
    exact he

/-- **The composition: a backward step of size `p` and a forward agreement
of length `e₀` give an agreement of length `e₀ + p` at the
backward-shifted pair.**

The proof is the arc computation described in the §4a docstring: for a
position `k` of the new window, either `k < p`, in which case it is read
from the backward agreement at `j = p - 1 - k` (the position `a-1-j` of the
new window is `a-p+k`), or `p ≤ k`, in which case it is read from the
forward agreement at `k - p`.  Both readings are of the two symbols shifted
by the *same* amount from `a` and from `b`, which is what makes them
comparable. -/
theorem agrees_of_backAgrees {a b : Fin G} {e₀ p : ℕ} (hp : p ≤ G)
    (hf : Agrees hG S e₀ a b) (hb : BackAgrees hG S a b p) :
    Agrees hG S (e₀ + p) ((prevPos hG)^[p] a) ((prevPos hG)^[p] b) := by
  have hbe : BackAgreesE hG S a b p :=
    (backAgrees_iff_backAgreesE hG S a b p hp).mp hb
  have hA : Nat.ModEq G ((prevPos hG)^[p] a).val (a.val + G - p) := by
    rw [backResidue hG p a hp]
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ hG)
  have hB : Nat.ModEq G ((prevPos hG)^[p] b).val (b.val + G - p) := by
    rw [backResidue hG p b hp]
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ hG)
  intro k
  by_cases hk : k.val < p
  · -- the position is read from the backward agreement, at `j = p-1-k`
    have h := hbe (p - 1 - k.val) (by omega)
    have hja : Nat.ModEq G (((prevPos hG)^[p] a).val + k.val) (a.val + G - 1 - (p - 1 - k.val)) := by
      have hme := hA.add_right k.val
      rw [show a.val + G - p + k.val = a.val + G - 1 - (p - 1 - k.val) from by omega] at hme
      exact hme
    have hjb : Nat.ModEq G (((prevPos hG)^[p] b).val + k.val) (b.val + G - 1 - (p - 1 - k.val)) := by
      have hme := hB.add_right k.val
      rw [show b.val + G - p + k.val = b.val + G - 1 - (p - 1 - k.val) from by omega] at hme
      exact hme
    calc cyc hG S (((prevPos hG)^[p] a).val + k.val)
        = cyc hG S (((prevPos hG)^[p] a).val + k.val % G) := cyc_add hG S _ _
      _ = cyc hG S ((((prevPos hG)^[p] a).val + k.val) % G) := cyc_add_mod hG S _ _
      _ = cyc hG S ((a.val + G - 1 - (p - 1 - k.val)) % G) := cyc_congr_modEq hG S hja
      _ = cyc hG S (a.val + G - 1 - (p - 1 - k.val)) := (cyc_mod' hG S _).symm
      _ = cyc hG S (b.val + G - 1 - (p - 1 - k.val)) := h
      _ = cyc hG S ((b.val + G - 1 - (p - 1 - k.val)) % G) := cyc_mod' hG S _
      _ = cyc hG S ((((prevPos hG)^[p] b).val + k.val) % G) := (cyc_congr_modEq hG S hjb).symm
      _ = cyc hG S (((prevPos hG)^[p] b).val + k.val % G) := (cyc_add_mod hG S _ _).symm
      _ = cyc hG S (((prevPos hG)^[p] b).val + k.val) := (cyc_add hG S _ _).symm
  · -- the position is read from the forward agreement, at `k - p`
    have hke : k.val - p < e₀ := by omega
    have h : cyc hG S (a.val + (k.val - p)) = cyc hG S (b.val + (k.val - p)) := by
      simpa using hf ⟨k.val - p, hke⟩
    calc cyc hG S (((prevPos hG)^[p] a).val + k.val)
        = cyc hG S (((prevPos hG)^[p] a).val + k.val % G) := cyc_add hG S _ _
      _ = cyc hG S ((((prevPos hG)^[p] a).val + k.val) % G) := cyc_add_mod hG S _ _
      _ = cyc hG S ((a.val + G - p + k.val) % G) :=
        cyc_congr_modEq hG S (hA.add_right k.val)
      _ = cyc hG S (a.val + G - p + k.val) := (cyc_mod' hG S _).symm
      _ = cyc hG S (a.val + (k.val - p)) := by
          rw [show a.val + G - p + k.val = (a.val + (k.val - p)) + G from by omega,
            cyc_add_G hG S]
      _ = cyc hG S (b.val + (k.val - p)) := h
      _ = cyc hG S (b.val + (k.val - p) + G) := (cyc_add_G hG S _).symm
      _ = cyc hG S ((b.val + G - p + k.val) % G) := by
          rw [show b.val + (k.val - p) + G = b.val + G - p + k.val from by omega,
            cyc_mod' hG S]
      _ = cyc hG S ((((prevPos hG)^[p] b).val + k.val) % G) :=
        (cyc_congr_modEq hG S (hB.add_right k.val)).symm
      _ = cyc hG S (((prevPos hG)^[p] b).val + k.val % G) := (cyc_add_mod hG S _ _).symm
      _ = cyc hG S (((prevPos hG)^[p] b).val + k.val) := (cyc_add hG S _ _).symm

/-! ### 4a.3 The periodic case, and why primitivity is the only thing needed for it

The composition of §4a.2 needs `p ≤ G`, i.e. it needs the backward step to
stop strictly inside one turn.  §3a's `max_back_agrees` allows the
exceptional value `p = G`, and that value is not a technicality: it says the
word is invariant under the shift `a ↦ b` at *every* position of the
circle, i.e. that the shift is a period.  A primitive word has no such
shift, so `p = G` is impossible at two distinct occurrences --- and
*impossible for no other reason*.  This is the rigorous form of the
"primality keeps the maximal extension below `G`" remark of
`docs/bbt-eulerian-cycle-89.md` §6, and it is the only place in this module
where a primitivity hypothesis is used. -/

/-- **A backward agreement of a full turn forces shift-invariance, hence
non-primitivity.**  `BackAgrees G a b` at two distinct starts says the word
is invariant under the shift from `a` to `b` at every position of the
circle: reindexing by `j = G - 1 - d` turns the `G` backward positions into
the `G` forward positions of the arc starting at `a`.  This is
`RepeatAdapter.not_primitive_of_ge_G_agree`, at the residue form. -/
theorem not_primitive_of_backAgrees_G {a b : Fin G} (hab : a ≠ b)
    (hb : BackAgrees hG S a b G) : ¬ RepeatAdapter.IsPrimitive hG S := by
  have hbe : BackAgreesE hG S a b G :=
    (backAgrees_iff_backAgreesE hG S a b G (by omega)).mp hb
  have hag : ∀ d : ℕ, d < G →
      cyc hG S (a.val + d) = cyc hG S (b.val + d) := by
    intro d hd
    have h := hbe (G - 1 - d) (by omega)
    have e1 : a.val + G - 1 - (G - 1 - d) = a.val + d := by omega
    have e2 : b.val + G - 1 - (G - 1 - d) = b.val + d := by omega
    rw [e1, e2] at h
    exact h
  have hab' : a.val % G ≠ b.val % G := by
    intro h
    apply hab
    apply Fin.ext
    exact mod_inj_of_lt hG a.isLt b.isLt h
  exact RepeatAdapter.not_primitive_of_ge_G_agree hG S a.val b.val G hab' (le_refl G) hag

/-- **The periodic case is excluded, in the only form needed: at two
distinct occurrences of a primitive word the maximal backward agreement is
below `G`.**  This is the composition-hypothesis of §4a.2 discharged for the
`p` of `max_back_agrees`. -/
theorem exists_backStep_lt_G {a b : Fin G} (hab : a ≠ b) (hprim : RepeatAdapter.IsPrimitive hG S) :
    ∃ p : ℕ, p < G ∧ BackAgrees hG S a b p ∧ ¬ BackAgrees hG S a b (p + 1) := by
  obtain ⟨p, hp, hbp, hnb⟩ := max_back_agrees hG S a b
  by_cases hlt : p < G
  · exact ⟨p, hlt, hbp, hnb hlt⟩
  · have hpG : p = G := by omega
    have hbpG : BackAgrees hG S a b G := by rw [hpG] at hbp; exact hbp
    exact (not_primitive_of_backAgrees_G hG S hab hbpG hprim).elim

/-! ### 4a.4 The backward step is a rotation: cyclic order is preserved

The maximal repeats of §4a.5 are built at the *shifted* starts
`prevPos^[p] a`, `prevPos^[p] b`, so the dichotomy has to be able to read
cyclic order at those starts.  The good news, recorded here, is that the
backward step is a rotation of the circle, so every arc relation --- in
particular `InOpenArc`, and hence `Interleaved` --- is unaffected by it.
This is the "correct cyclic-order relationship" the `#89` route needs: the
maximal repeat of a branch pair sits at a rotation of the pair, so an
interleaving of two such repeats is an interleaving of the two branch
occurrence pairs, and conversely. -/

/-- **The backward step preserves open arcs.**  For `p ≤ G`, three
occurrences lie in the open clockwise arc from `a` to `b` iff they do so
after all three are stepped backwards by `p`.  This is the rotation
invariance that lets the dichotomy of §4a.5 be phrased at the shifted
starts. -/
theorem openArc_backward {a b c : Fin G} {p : ℕ} (hp : p ≤ G) :
    InOpenArc (mkGenome hG S) a b c ↔
      InOpenArc (mkGenome hG S) ((prevPos hG)^[p] a) ((prevPos hG)^[p] b) ((prevPos hG)^[p] c) := by
  have hres : ∀ x : Fin G, (prevPos hG)^[p] x = ⟨(x.val + G - p) % G, Nat.mod_lt _ hG⟩ :=
    fun x => backResidue hG p x hp
  have hlt : ∀ x : Fin G, ((prevPos hG)^[p] x).val < G := by
    intro x
    rw [hres x]
    exact Nat.mod_lt _ hG
  have hmod : ∀ x : Fin G, Nat.ModEq G (x.val + G - p) ((prevPos hG)^[p] x).val := by
    intro x
    have e : ((prevPos hG)^[p] x).val % G = (x.val + G - p) % G := by
      rw [hres x]
      exact Nat.mod_eq_of_lt (Nat.mod_lt _ hG)
    exact e.symm
  have key : ∀ (u v : Fin G),
      (((prevPos hG)^[p] u).val + G - ((prevPos hG)^[p] v).val) % G
        = (u.val + G - v.val) % G := by
    intro u v
    have hsub := Nat.ModEq.sub (n := G)
      (a := ((prevPos hG)^[p] u).val + G) (b := (u.val + G - p) + G)
      (c := ((prevPos hG)^[p] v).val) (d := v.val + G - p)
      (Nat.le_trans (hlt v).le (Nat.le_add_left _ _))
      (by have := v.isLt; have := hp; omega)
      ((hmod u).add_right G).symm (hmod v).symm
    rw [show (u.val + G - p) + G - (v.val + G - p) = u.val + G - v.val from by omega] at hsub
    exact hsub
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · unfold InOpenArc at h ⊢
    simp only [len_mkGenome] at h ⊢
    obtain ⟨h1, h2⟩ := h
    have h3 := key c a
    have h4 := key b a
    rw [h3, h4]
    exact ⟨h1, h2⟩
  · unfold InOpenArc at h ⊢
    simp only [len_mkGenome] at h ⊢
    obtain ⟨h1, h2⟩ := h
    have h3 := key c a
    have h4 := key b a
    rw [h3] at h1 h2
    rw [h4] at h2
    exact ⟨h1, h2⟩

/-- **... and therefore preserves interleavings, at a common step count.**
Two pairs of occurrences that interleave still interleave after all four
starts are stepped backwards by the same amount.

The common step count is not a technicality, and the reason is worth
recording for the dichotomy.  Backward iteration is injective *at a fixed
step count* (`prevIter_ne`), so pairwise distinctness is preserved there; but
two *different* step counts can collide, e.g. `prevPos^[1] 1 = prevPos^[2] 2` on
the circle.  So one may not transport an interleaving from two pairs of
branch occurrences to the two maximal repeats built out of them when the two
pairs needed different backward steps.  The dichotomy of step 3 therefore
has to use the interleaving of the two maximal repeats' starts as a
*hypothesis* (`LongObstruction`'s second disjunct), which is where
`interleaved_disjunct` consumes it, rather than deduce it. -/
theorem interleaved_backward {a b c d : Fin G} {p : ℕ} (hp : p ≤ G)
    (h : Interleaved (mkGenome hG S) a b c d) :
    Interleaved (mkGenome hG S) ((prevPos hG)^[p] a) ((prevPos hG)^[p] b)
      ((prevPos hG)^[p] c) ((prevPos hG)^[p] d) := by
  obtain ⟨hff, har⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hff
  have hfd : @FourDistinct α (mkGenome hG S) ((prevPos hG)^[p] a) ((prevPos hG)^[p] b)
      ((prevPos hG)^[p] c) ((prevPos hG)^[p] d) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e; exact h1 (prevIter_injective hG p e)
    · intro e; exact h2 (prevIter_injective hG p e)
    · intro e; exact h3 (prevIter_injective hG p e)
    · intro e; exact h4 (prevIter_injective hG p e)
    · intro e; exact h5 (prevIter_injective hG p e)
    · intro e; exact h6 (prevIter_injective hG p e)
  have hb : ∀ x : Fin G, InOpenArc (mkGenome hG S) a b x ↔
      InOpenArc (mkGenome hG S) ((prevPos hG)^[p] a) ((prevPos hG)^[p] b) ((prevPos hG)^[p] x) := by
    intro x
    exact openArc_backward hG S (a := a) (b := b) (c := x) (p := p) hp
  refine And.intro hfd ?_
  refine Iff.intro (fun hc => ?_) (fun hd => ?_)
  · exact fun hd => har.mp ((hb c).mpr hc) ((hb d).mpr hd)
  · have hnd : ¬ InOpenArc (mkGenome hG S) a b d := fun hd' => hd ((hb d).mp hd')
    exact (hb c).mp (har.mpr hnd)

/-! ### 4a.5 The backward maximal extension of a branch pair

The theorem the `#89` route consumes.  Two distinct occurrences of one
`(L-1)`-mer, at *arbitrary* starts, lie inside a maximal repeat of length
`≥ L - 1` whose two starts are the two occurrences shifted backwards by the
*same* amount `p` --- the maximal backward step.  No `Preceding a ≠
Preceding b` hypothesis is required, which is exactly what §3 shows is not
available; primitivity is required, and only to exclude the periodic case
of §4a.3. -/

/-- **An agreement of length `L - 1` is a shared vertex** of the
`(L-1)`-mer multigraph, i.e. the branch-object hypothesis of §2 in
`Agrees` form.  (`vtx` is `nodeWindow`, `fun d => cyc hG S (r.val + d)`.) -/
theorem vtx_eq_of_agrees {L : ℕ} {a b : Fin G} (hag : Agrees hG S (L - 1) a b) :
    vtx hG L S a = vtx hG L S b := by
  funext d
  exact hag ⟨d.val, d.isLt⟩

/-- **The backward maximal extension of a branch pair.**  See the section
docstring.  The two starts of the resulting maximal repeat are
`prevPos^[p] a` and `prevPos^[p] b`, so they are the branch occurrences
moved back together by one and the same amount --- the maximal backward
step, which is exactly the `p` whose failure gives the preceding-symbol
difference of `preceding_ne_of_max_back`. -/
theorem maximalRepeat_of_branch_backward {L : ℕ} (hL : 2 ≤ L) {a b : Fin G}
    (hab : a ≠ b) (hvt : vtx hG L S a = vtx hG L S b)
    (hprim : RepeatAdapter.IsPrimitive hG S) :
    ∃ (p e : Fin G), (mkGenome hG S).IsRepeat e
        ((prevPos hG)^[p.val] a) ((prevPos hG)^[p.val] b) ∧ L - 1 ≤ e.val := by
  obtain ⟨p, hp, hbp, hnb⟩ := exists_backStep_lt_G hG S hab hprim
  have hq : p ≤ G := Nat.le_of_lt hp
  -- the two occurrences of the branch object spell the same `(L-1)`-mer ...
  have hag0 : Agrees hG S (L - 1) a b := fun d => congrFun hvt d
  -- ... and so do the occurrences moved back together by the maximal backward
  -- step: the composition of §4a.2, which adds the `p` backward positions to
  -- the forward window.
  have hag1 : Agrees hG S ((L - 1) + p) ((prevPos hG)^[p] a) ((prevPos hG)^[p] b) :=
    agrees_of_backAgrees hG S hq hag0 hbp
  have hag2 : Agrees hG S (L - 1) ((prevPos hG)^[p] a) ((prevPos hG)^[p] b) :=
    agrees_mono hG S (by omega) hag1
  -- and their preceding symbols differ, by maximality of the backward step
  have hprec : (mkGenome hG S).Preceding ((prevPos hG)^[p] a)
      ≠ (mkGenome hG S).Preceding ((prevPos hG)^[p] b) :=
    preceding_ne_of_max_back hG S a b hp hbp hnb
  obtain ⟨e, he, hlen⟩ :=
    maximalRepeat_of_branch (L := L) (α := α) hG S hL (prevIter_ne hG hq hab)
      (vtx_eq_of_agrees hG S hag2) hprec
  exact ⟨⟨p, hp⟩, e, he, hlen⟩

/-! ### 4a.6 A kernel-checked instance of the whole backward route -/

/-- The word `S0111` of §3 is **primitive**: it is not a power.  The
maximal-extension route of §4a.5 is stated for a primitive truth, so this
instance is the one on which that route is exercised. -/
theorem S0111_primitive : RepeatAdapter.IsPrimitive hG4b S0111 := by
  rintro s hs hsG hsi
  have hcases : s = 1 ∨ s = 2 ∨ s = 3 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact absurd (hsi 0) (by decide)
  · exact absurd (hsi 0) (by decide)
  · exact absurd (hsi 0) (by decide)

/-- ... and the backward maximal extension of its branch pair `2`, `3` is
available: the primitive truth of the previous lemma turns the branch pair
`2`, `3` --- whose preceding symbols agree, so which carries no maximal
repeat at all (§3) --- into a maximal repeat of length `≥ L-1 = 1`, at the
two occurrences moved back together by the same maximal backward step.  The
concrete maximal repeat at the pair `1`, `2` is `maximalRepeat_of_branch_0111`
of §3, and the step of the present lemma is `p = 2`, since
`prevPos^[2] 2 = 1` and `prevPos^[2] 3 = 2`. -/
theorem maximalRepeat_branch_backward_0111 :
    ∃ (p e : Fin 4), (mkGenome hG4b S0111).IsRepeat e
        ((prevPos hG4b)^[p.val] (2 : Fin 4)) ((prevPos hG4b)^[p.val] (3 : Fin 4)) ∧
      (2 - 1 : ℕ) ≤ e.val := by
  have hab : (2 : Fin 4) ≠ 3 := by decide
  have hvt : vtx hG4b 2 S0111 (2 : Fin 4) = vtx hG4b 2 S0111 (3 : Fin 4) := by decide
  exact maximalRepeat_of_branch_backward hG4b S0111 (by decide) hab hvt S0111_primitive

/- ## 5. The remaining gap, stated and left open

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
