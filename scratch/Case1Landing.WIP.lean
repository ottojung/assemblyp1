import AssemblyP1.BBTMaximalExtension

/-!
# Case 1 of §5 of `/workspace/BOARD94-BADNESS-0153.md`: the backward step of a
# preceding-blocked constituent (issue #89, board 94)

This module works on the case-1 residual left open by
`/workspace/BOARD94-CASE1-0320.md` §6 and §9 of
`/workspace/BOARD94-CASE3-0300.md`: two interleaved constituents carrying the
same `(L−1)`-mers, one **unblocked** (`Preceding a ≠ Preceding b`) and one
**blocked** (`Preceding c = Preceding d`, maximal backward step `p`), on a genome
with **no long obstruction**.  The claim is that the blocked pair's maximal
repeat is the *same* maximal repeat as the unblocked pair's, i.e.

```text
p = distVal a c = distVal b d
```

(`case1_landing`, §5).  It is **not proved here**: it is a `Prop`, with no
`axiom`, no `sorry`, no `admit`.

What *is* proved here, kernel-checked, is the first half of the residual:

* `case1_no_small_step` (**§4**): at a case-1 configuration on a genome with no
  long obstruction, the blocked constituent's maximal backward step `p` cannot be
  smaller than `min (distVal a c) (distVal b d)`.  Equivalently, a maximal
  backward step that lands strictly *inside* the two gaps of the configuration
  produces a `LongObstruction`.  This is the "the `p < min(u,w)` half follows
  from interleaving" step of the predecessor's §6, now a theorem.

Two conventions that this module fixes and that the rest of the project should
respect:

* `BackAgrees q` (`AssemblyP1.BBTMaximalExtension`) is the agreement at the `q`
  positions **strictly preceding** the two starts (`d = 0` reads position
  `a − 1`).  So a pair whose preceding symbols differ has maximal backward step
  `0`, and stepping a pair back `p` places lands it at
  `(prevPos^[p] a, prevPos^[p] b)`.
* `distVal x y = (y.val + G − x.val) % G` is the clockwise distance from `x` to
  `y`, and `InOpenArc x y z ↔ 0 < distVal x z < distVal x y`.

The helpers in §§1–3 (`prevPos_inj`, `prevPos_iter_inj`, `distVal`,
`inOpenArc_iff`, `cyc_turn`, `cyc_prev_fwd`, `backAgrees_shift`,
`agrees_back_step`, `agrees_back`) restate, under this module's own names,
lemmas that already exist in `AssemblyP1.BBTReplacementInvariant` §7.  They are
duplicated rather than imported because that module's `.olean` cannot be built
on this host — `lake build` there recompiles the whole Mathlib dependency tree
and damages the shared cache (see `/workspace/BOARD94-CASE1-0320.md` §10) — so
this module imports only modules that are already built, and is checkable with
`lake env lean`.  A successor with a working `lake build` should delete this
duplication and import §7 instead.
-/

namespace AssemblyP1.Case1Landing

open SourceFaithfulIs
open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open OrientedRigidity

set_option linter.unusedSectionVars false

/-! ## 1. Clockwise distances and stepping backwards -/

section Base

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α)

/-- One-step backward rotation is injective. -/
lemma prevPos_inj {x y : Fin G} : prevPos hG x = prevPos hG y → x = y := by
  intro hxy
  calc x = nextPos hG (prevPos hG x) := (nextPrev _ _).symm
    _ = nextPos hG (prevPos hG y) := by rw [hxy]
    _ = y := nextPrev _ _

lemma prevPos_iter_inj : ∀ (q : ℕ) {x y : Fin G},
    (prevPos hG)^[q] x = (prevPos hG)^[q] y → x = y := by
  intro q
  induction q with
  | zero => intro x y h; exact h
  | succ q ih =>
    intro x y h
    have h' : prevPos hG x = prevPos hG y := ih (by
      simpa only [Function.iterate_succ_apply] using h)
    exact prevPos_inj (hG := hG) h'

/-- **Clockwise distance from `x` to `y`.** -/
def distVal (x y : Fin G) : ℕ := (y.val + G - x.val) % G

lemma distVal_lt (hG : 0 < G) {x y : Fin G} : distVal x y < G := by
  simp only [distVal]; exact Nat.mod_lt _ hG

/-- Distance zero is coincidence. -/
lemma distVal_eq_zero {x y : Fin G} : distVal x y = 0 ↔ x = y := by
  constructor
  · intro h
    have _ := x.isLt
    have _ := y.isLt
    simp only [distVal] at h
    have hlt : y.val - x.val < G := by omega
    have hz : y.val - x.val = 0 := by
      rw [show y.val + G - x.val = (y.val - x.val) + G from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hlt] at h
      exact h
    exact Fin.ext (by omega)
  · intro h
    simp only [distVal, h]
    rw [show y.val + G - y.val = G from by omega, Nat.mod_self]

/-- **The arc test in terms of distances.** -/
lemma inOpenArc_iff {x y z : Fin G} :
    InOpenArc (mkGenome hG S) x y z ↔ (0 < distVal x z ∧ distVal x z < distVal x y) := by
  unfold InOpenArc distVal
  rfl

lemma mod_add_G (m : ℕ) : m + G ≡ m [MOD G] := by
  have h1 := (Nat.mod_modEq (m + G) G).symm
  have h2 : (m + G) % G = m % G := Nat.add_mod_right _ _
  rw [h2] at h1
  exact h1.trans (Nat.mod_modEq m G)

/-- **Distance is additive along the circle when it does not wrap.** -/
lemma distVal_sub (hG : 0 < G) {x y z : Fin G} (h : distVal x y ≤ distVal x z) :
    distVal x y + distVal y z = distVal x z := by
  have key : distVal x y + distVal y z ≡ distVal x z [MOD G] := by
    simp only [distVal]
    refine ((Nat.mod_modEq (y.val + G - x.val) G).add
      (Nat.mod_modEq (z.val + G - y.val) G)).trans ?_
    rw [show y.val + G - x.val + (z.val + G - y.val) = (z.val + G - x.val) + G from by omega]
    exact (mod_add_G (G := G) (z.val + G - x.val)).trans
      ((Nat.mod_modEq (z.val + G - x.val) G).symm)
  have h4 := Nat.ModEq.sub_right (by omega) h key
  have hB : (distVal x y + distVal y z) - distVal x y = distVal y z := by omega
  have hltB : distVal y z < G := distVal_lt hG
  have hltZ : distVal x z < G := distVal_lt hG (x := x) (y := z)
  have hltC : distVal x z - distVal x y < G := by omega
  rw [hB] at h4
  have h5 : distVal y z % G = (distVal x z - distVal x y) % G := h4
  rw [Nat.mod_eq_of_lt hltB, Nat.mod_eq_of_lt hltC] at h5
  omega

/-- **Stepping one place back from a fixed anchor subtracts one.** -/
lemma distVal_prev (x y : Fin G) :
    distVal x (prevPos hG y) = (distVal x y + G - 1) % G := by
  have hA : (y.val + G - 1) % G + G - x.val = (y.val + G - 1) % G + (G - x.val) := by
    have _ := x.isLt
    omega
  have hB : (y.val + G - x.val) % G + G - 1 = (y.val + G - x.val) % G + (G - 1) := by
    omega
  simp only [distVal, prevPos]
  rw [hA, hB]
  have h1 := (Nat.mod_modEq (y.val + G - 1) G).add_right (G - x.val)
  have h2 := (Nat.mod_modEq (y.val + G - x.val) G).add_right (G - 1)
  have h3 : y.val + G - 1 + (G - x.val) = y.val + G - x.val + (G - 1) := by
    have _ := x.isLt
    omega
  exact h1.trans (by rw [h3]; exact h2.symm)

lemma distVal_dec_one {v : ℕ} (h1 : 1 ≤ v) (hG1 : v < G) : (v + G - 1) % G = v - 1 := by
  rw [show v + G - 1 = (v - 1) + G from by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- **Stepping `q < distVal x y` places back from `x` lands `q` places before
`y`, measured from `x`.** -/
lemma distVal_prev_iter : ∀ (q : ℕ) (x y : Fin G), q < distVal x y →
    distVal x ((prevPos hG)^[q] y) = distVal x y - q := by
  intro q
  induction q with
  | zero => intro x y _; simp
  | succ q ih =>
    intro x y hq
    have e : (prevPos hG)^[q + 1] y = prevPos hG ((prevPos hG)^[q] y) :=
      Function.iterate_succ_apply' (prevPos hG) q y
    rw [e, distVal_prev]
    have hq' : q < distVal x y := by omega
    rw [ih x y hq']
    have hvx := distVal_lt hG (x := x) (y := y)
    have hv : distVal x y - q < G := by omega
    have h1 : 1 ≤ distVal x y - q := by omega
    rw [distVal_dec_one h1 hv]
    omega

end Base

/-! ## 2. reading symbols one place back -/

section Symbols

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α)

lemma cyc_turn (i : ℕ) : cyc hG S (i + G) = cyc hG S i := by
  simp [cyc]

lemma cyc_prev_step (x : Fin G) (i : ℕ) :
    cyc hG S ((prevPos hG x).val + i) = cyc hG S (x.val + G - 1 + i) := by
  have h1 : ((prevPos hG x).val + i) % G = (x.val + G - 1 + i) % G := by
    simp only [prevPos]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  simp only [cyc]
  congr 1
  exact Fin.ext h1

lemma cyc_prev_fwd (x : Fin G) (j : ℕ) :
    cyc hG S ((prevPos hG x).val + (j + 1)) = cyc hG S (x.val + j) := by
  rw [cyc_prev_step hG S x (j + 1)]
  have key : x.val + G - 1 + (j + 1) = (x.val + j) + G := by omega
  rw [key]
  exact cyc_turn hG S (x.val + j)

end Symbols

/-! ## 3. composing a backward step with a forward agreement -/

section Backward

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α)

lemma backAgrees_shift {a b : Fin G} {p q : ℕ}
    (hag : BackAgrees hG S a b (p + q)) :
    BackAgrees hG S ((prevPos hG)^[q] a) ((prevPos hG)^[q] b) p := by
  intro e
  simp only [BackAgrees] at hag ⊢
  have hlt : e.val + q < p + q := by omega
  have h := hag ⟨e.val + q, hlt⟩
  have keyA : (prevPos hG)^[e.val + q] a
      = (prevPos hG)^[e.val] ((prevPos hG)^[q] a) :=
    Function.iterate_add_apply (prevPos hG) e.val q a
  have keyB : (prevPos hG)^[e.val + q] b
      = (prevPos hG)^[e.val] ((prevPos hG)^[q] b) :=
    Function.iterate_add_apply (prevPos hG) e.val q b
  rw [← keyA, ← keyB]
  exact hag ⟨e.val + q, hlt⟩

lemma agrees_back_step {a b : Fin G} {e₀ : ℕ}
    (hag : Agrees hG S e₀ a b) (h1 : BackAgrees hG S a b 1) :
    Agrees hG S (e₀ + 1) (prevPos hG a) (prevPos hG b) := by
  intro d
  refine Fin.cases ?case0 (fun j => ?_) d
  · simpa using h1 (0 : Fin 1)
  · simp only [BackAgrees] at h1
    simp only [Fin.val_succ]
    rw [cyc_prev_fwd hG S a j.val, cyc_prev_fwd hG S b j.val]
    exact hag ⟨j.val, by omega⟩

/-- **THE INDEX ARITHMETIC.**  A backward agreement of `p` places together with
a forward agreement of `e₀` places is a forward agreement of `e₀ + p` places at
the occurrences stepped `p` places back. -/
lemma agrees_back : ∀ (p e₀ : ℕ) (a b : Fin G),
    BackAgrees hG S a b p → Agrees hG S e₀ a b →
    Agrees hG S (e₀ + p) ((prevPos hG)^[p] a) ((prevPos hG)^[p] b) := by
  intro p
  induction p with
  | zero =>
    intro e₀ a b _ hag
    simpa only [Function.iterate_zero, id_eq, Nat.add_zero] using hag
  | succ p ih =>
    intro e₀ a b hagp hag
    have h1 : BackAgrees hG S a b 1 := by
      intro d
      match d with
      | ⟨0, _⟩ => exact hagp ⟨1, by omega⟩
    have h2 : BackAgrees hG S (prevPos hG a) (prevPos hG b) p :=
      backAgrees_shift (hG := hG) (S := S) (a := a) (b := b) (p := p) (q := 1) hagp
    rw [Function.iterate_succ_apply (prevPos hG) p a, Function.iterate_succ_apply (prevPos hG) p b]
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (ih (e₀ := e₀ + 1) (a := prevPos hG a) (b := prevPos hG b) h2
        (agrees_back_step (hG := hG) (S := S) hag h1))

lemma agrees_imp_vtx {L e : ℕ} {x y : Fin G} (hag : Agrees hG S e x y)
    (he : L - 1 ≤ e) : vtx hG L S x = vtx hG L S y := by
  funext d
  have hd : d.val < e := lt_of_lt_of_le d.isLt he
  exact hag ⟨d.val, hd⟩

end Backward

/-! ## 4. the small-step half of the case-1 residual, kernel-checked -/

section SmallStep

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α)

/-- **A backward step that stays strictly inside both gaps of the interleaved
configuration keeps the stepped-back pair interleaved with the unblocked pair.**
`hinn` is the orientation choice: it says the blocked constituent's first start
`c` is the one on the open arc from `a` to `b`, which is available up to
interchanging `c` and `d` — interchanging them preserves `Interleaved`, the
`vtx` clause, the `Preceding` clause and the backward agreement, and only
renames the two gaps. -/
lemma interleaved_stepped {a b c d : Fin G} {r : ℕ}
    (hIA : Interleaved (mkGenome hG S) a b c d)
    (hinn : InOpenArc (mkGenome hG S) a b c)
    (hr1 : r < distVal a c) (hr2 : r < distVal b d) :
    Interleaved (mkGenome hG S) a b ((prevPos hG)^[r] c) ((prevPos hG)^[r] d) := by
  have hc := (inOpenArc_iff hG S).mp hinn
  have hIA' := hIA.2.mp hinn
  have hdnot := (inOpenArc_iff hG S).mp hIA'
  have hne : a ≠ d := hIA.1.2.2.1
  have hzd : distVal a d ≠ 0 := fun h => hne (distVal_eq_zero (G := G) hG.mp h)
  have hle : distVal a b ≤ distVal a d := by omega
  have had : distVal b d + distVal a b = distVal a d :=
    distVal_sub hG (x := a) (y := b) (z := d) hle
  have hpc : distVal a ((prevPos hG)^[r] c) = distVal a c - r :=
    distVal_prev_iter (hG := hG) r a c hr1
  have hpd : distVal a ((prevPos hG)^[r] d) = distVal a d - r := by
    refine distVal_prev_iter (hG := hG) r a d ?_
    rw [← had]
    omega
  have hia1 : InOpenArc (mkGenome hG S) a b ((prevPos hG)^[r] c) := by
    rw [inOpenArc_iff hG S]
    omega
  have hia2 : ¬ InOpenArc (mkGenome hG S) a b ((prevPos hG)^[r] d) := by
    rw [inOpenArc_iff hG S]
    omega
  have h1 : (prevPos hG)^[r] a ≠ (prevPos hG)^[r] b := by
    intro h; exact hIA.1.1 (prevPos_iter_inj (hG := hG) r h)
  have h2 : a ≠ (prevPos hG)^[r] c := by
    intro h
    have hz : distVal a ((prevPos hG)^[r] c) = 0 := by rw [hpc]; omega
    exact (distVal_eq_zero (G := G) hG).mp hz h
  have h3 : a ≠ (prevPos hG)^[r] d := by
    intro h
    have hz : distVal a ((prevPos hG)^[r] d) = 0 := by rw [hpd]; omega
    exact (distVal_eq_zero (G := G) hG).mp hz h
  have h4 : b ≠ (prevPos hG)^[r] c := by
    intro h
    have hz : distVal a ((prevPos hG)^[r] c) = distVal a b := by rw [hpc]; omega
    omega
  have h5 : b ≠ (prevPos hG)^[r] d := by
    intro h
    have hz : distVal a ((prevPos hG)^[r] d) = distVal a b := by rw [hpd]; omega
    omega
  have h6 : (prevPos hG)^[r] c ≠ (prevPos hG)^[r] d := by
    intro h
    have hz : distVal a ((prevPos hG)^[r] c) = distVal a ((prevPos hG)^[r] d) := by
      rw [hpc, hpd]
    omega
  exact ⟨⟨h1, h2, h3, h4, h5, h6⟩, iff_of_true hia1 hia2⟩

/-- **THE SMALL-STEP HALF OF THE CASE-1 RESIDUAL, kernel-checked.**  At a
case-1 configuration on a genome with **no long obstruction**, the blocked
constituent's maximal backward step `p` is **not** smaller than
`min (distVal a c) (distVal b d)`.

Equivalently: a maximal backward step that lands strictly inside the two gaps of
the configuration turns the genome into a `LongObstruction`.  Nothing genome-side
is assumed here: the only genome hypothesis is `¬ LongObstruction`, and the
`Preceding` clauses are hypotheses *of the configuration*, never conclusions; in
particular the circular genome-side `Preceding` clause of §5 is not used. -/
theorem case1_no_small_step {L : ℕ} (hL : 2 ≤ L) {a b c d : Fin G} (p : ℕ)
    (hno : ¬ LongObstruction hG L S)
    (hIA : Interleaved (mkGenome hG S) a b c d)
    (hinn : InOpenArc (mkGenome hG S) a b c)
    (hva : vtx hG L S a = vtx hG L S b) (hvc : vtx hG L S c = vtx hG L S d)
    (hprec : (mkGenome hG S).Preceding a ≠ (mkGenome hG S).Preceding b)
    (hprec' : (mkGenome hG S).Preceding c = (mkGenome hG S).Preceding d)
    (hbp : BackAgrees hG S c d p) (hbp' : ¬ BackAgrees hG S c d (p + 1))
    (hsmall : p < min (distVal a c) (distVal b d)) :
    False := by
  have hpG : p < G := by
    have := distVal_lt (hG := hG) (x := a) (y := c)
    omega
  have hagcd : Agrees hG S (L - 1) c d := fun d => congrFun hvc d
  have hA2 : Agrees hG S (L - 1 + p) ((prevPos hG)^[p] c) ((prevPos hG)^[p] d) :=
    agrees_back (α := α) (hG := hG) (S := S) (p := p) (e₀ := L - 1) c d hbp hagcd
  have hvt2 : vtx hG L S ((prevPos hG)^[p] c) = vtx hG L S ((prevPos hG)^[p] d) :=
    agrees_imp_vtx (hG := hG) (S := S) hA2 (by omega)
  have hpr2 : (mkGenome hG S).Preceding ((prevPos hG)^[p] c)
      ≠ (mkGenome hG S).Preceding ((prevPos hG)^[p] d) :=
    preceding_ne_of_max_back (hG := hG) (S := S) c d hpG hbp hbp'
  have hne2 : (prevPos hG)^[p] c ≠ (prevPos hG)^[p] d :=
    fun h => hIA.1.2.2.2.2.2 (prevPos_iter_inj (hG := hG) p h)
  have hne1 : a ≠ b := hIA.1.1
  obtain ⟨e₁, he₁, hlen₁⟩ :=
    maximalRepeat_of_branch (α := α) (hG := hG) (S := S) (L := L) hL hne1 hva hprec
  obtain ⟨e₂, he₂, hlen₂⟩ :=
    maximalRepeat_of_branch (α := α) (hG := hG) (S := S) (L := L) hL hne2 hvt2 hpr2
  have hIA2 : Interleaved (mkGenome hG S) a b ((prevPos hG)^[p] c) ((prevPos hG)^[p] d) :=
    interleaved_stepped (hG := hG) (S := S) hIA hinn hsmall.1 hsmall.2
  exact hno (interleaved_disjunct (hG := hG) (S := S) he₁ he₂ hIA2 hlen₁ hlen₂)

end SmallStep

end AssemblyP1.Case1Landing