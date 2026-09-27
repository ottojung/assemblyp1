import AssemblyP1.BBTMaximalExtension
import AssemblyP1.BBTUniqueEulerian

/-!
# The fibre/period lemma for the `#89` dichotomy (#89)

`AssemblyP1.BBTMaximalExtension.EulerianCycleGap` is the remaining statement of
the `#89` route: an `Ukkonen` word has a **unique** Eulerian cycle in the
condensed `(L-1)`-mer multigraph.  Step 2 of the roadmap (the maximal
extension) is proved in `AssemblyP1/BBTMaximalExtension.lean`; what the
dichotomy of step 3 consumes on top of it is a bound on how many starts can
carry **one** `(L-1)`-mer, i.e. on the *fibres* of the vertex labelling
(`BBTSequenceGraph.fibre`).  This module proves exactly that bound, in the
form the period arithmetic supports.

The lemma is the following.  Write `p = leastPeriod`, and read
`p ∣ sh hG a b` as "`a` and `b` are congruent modulo the least period", the
relation of `BBTUniqueEulerian` §1.3.

> **Three occurrences of one vertex label.**  Let `a, b, c` be pairwise
> distinct starts carrying the same `(L-1)`-mer, with `2 ≤ L`.  Then either
> two of the three are congruent modulo `p`, or the three occurrences ---
> extended backwards as far as they agree --- carry a **maximal triple
> repeat** of length `≥ L - 1`.

Since `Ukkonen` forbids maximal triple repeats of length `≥ L - 1`
(`AssemblyP1.P2.Ukkonen`, first clause), the second alternative is a
`LongObstruction` and we get the collapse:

> **Under `Ukkonen`, three occurrences of one `(L-1)`-mer collapse modulo
> the least period.**  `three_occurrences_collapse_of_Ukkonen`.

Equivalently, with `classOf a = {x | p ∣ sh hG a x}` the *period class* of
`a`:

> **Under `Ukkonen`, the starts realising one vertex lie in at most two
> period classes** (`fibre_subset_two_classes`), and in the **primitive**
> case, where the least period is `G` and the classes are singletons, every
> fibre has at most two starts (`fibre_card_le_two_of_primitive`).

## Why the dichotomy is exhaustive (the content of the proof)

Take the maximal *forward* agreement `m ≤ G` of the three occurrences and the
maximal *backward* agreement `q ≤ G`; the maximal-extension machinery of
`AssemblyP1/BBTMaximalExtension` §2/§3a is reused verbatim, at the level of
three occurrences instead of two.

* If `m = G` the three occurrences agree for a full turn, so the shift
  `sh a b` is a period (`BBTUniqueEulerian.period_of_agree_all`) and `p`
  divides it: the collapse.
* If `q = G` the same holds, read backwards.
* Otherwise step the triple `q` positions backwards (`backAgr3F_add`): the
  shifted triple agrees on `q + m` consecutive positions, its preceding
  symbols are not all equal (maximality of `q`) and its following symbols are
  not all equal (maximality of `m`).  If `q + m ≥ G` the agreement covers a
  full turn and we are back at the first case, read back at the original
  occurrences by `agr3F_G_of_shifted`; if `q + m < G` those three facts
  *are* a `Genome.IsTripleRepeat` of length `q + m ≥ L - 1`.

No Fine--Wilf argument and no primitivity is used: the periodicity
alternative is detected by the full-turn agreement, exactly as
`BBTMaximalExtension.preceding_eq_of_agrees_ge` does for two occurrences.

## What is proved, and what is not

* **Proved (kernel-checked).**
  `three_occurrences_collapse_or_tripleRepeat` (the lemma above, with no
  hypothesis but `2 ≤ L` and distinctness of the three starts),
  `three_occurrences_collapse_of_Ukkonen`, the period-class arithmetic
  (`classOf`, `mem_classOf`, `mem_fibre_of_mem_classOf`,
  `classOf_subset_fibre`, `sameClass_trans`), the primitivity bridge
  (`shiftInvariant_of_period`, `leastPeriod_eq_G_of_primitive`,
  `sh_eq_zero_of_dvd_leastPeriod`, `classOf_singleton`), the fibre bounds
  `fibre_subset_two_classes` and `fibre_card_le_two_of_primitive`, and the
  cyclic-access and maximal-extension lemmas they use.
* **Not proved.**  `EulerianCycleGap` itself.  The lemma bounds the fibres of
  the vertex labelling: an `Ukkonen` word labels each `(L-1)`-mer at starts
  of at most two period classes, and in the primitive stratum at at most two
  starts.  The **interleaved** disjunct of the dichotomy --- two extended
  pairs of branch occurrences whose maximal extensions interleave --- is a
  separate step and is untouched: nothing here produces a second maximal
  repeat, so `BBTMaximalExtension.interleaved_disjunct` still has no
  supplier.  `EulerianCycleGap` remains a `Prop` with no inhabitant, and no
  axiom, `sorry` or `admit` is introduced here.
* **Not attempted.**  The counting form of the period-class bound,
  `card (classOf a) = G / leastPeriod` and hence
  `card (fibre v) ≤ 2 * (G / p)`.  It follows from the same collapse lemma
  plus `Nat.card_multiples'`, and is recorded in
  `docs/bbt-eulerian-cycle-89.md` §6a as the remaining arithmetic; it is not
  needed by the primitive case, which is the one the population chain uses.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AssemblyP1.BBTEulerian

open SourceFaithfulIs
open OrientedRigidity
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.RepeatAdapter

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α)

/-! ## 1. Cyclic access, spelled on the symbol level -/

/-- **Reading at a position of the circle.** -/
theorem cyc_fin (r : Fin G) : cyc hG S r.val = S r := by
  have h1 : cyc hG S r.val = S ⟨r.val % G, Nat.mod_lt _ hG⟩ := rfl
  have h2 : S ⟨r.val % G, Nat.mod_lt _ hG⟩ = S r :=
    congrArg (fun t : Fin G => S t) (Fin.ext (Nat.mod_eq_of_lt r.isLt))
  exact h1.trans h2

/-- **A whole turn changes nothing.** -/
theorem cyc_add_G (i : ℕ) : cyc hG S (i + G) = cyc hG S i := by
  have h1 : cyc hG S (i + G) = S ⟨(i + G) % G, Nat.mod_lt _ hG⟩ := rfl
  have h2 : cyc hG S i = S ⟨i % G, Nat.mod_lt _ hG⟩ := rfl
  have h3 : (i + G) % G = i % G := Nat.add_mod_right _ _
  exact h1.trans ((congrArg (fun t : Fin G => S t) (Fin.ext h3)).trans h2.symm)

/-- **Reducing a summand that was reduced already.**  The workhorse for
moving a start `rotAdd hG r a` back to the coordinate `a`: its value is
`(a.val + r) % G`, and the symbol at offset `v` past it is the symbol at
`a.val + r + v`. -/
theorem cyc_mod_add (u v : ℕ) : cyc hG S (u % G + v) = cyc hG S (u + v) := by
  have h1 : cyc hG S (u % G + v) = S ⟨(u % G + v) % G, Nat.mod_lt _ hG⟩ := rfl
  have h2 : cyc hG S (u + v) = S ⟨(u + v) % G, Nat.mod_lt _ hG⟩ := rfl
  have h' : Nat.ModEq G (u % G + v) ((u + v) % G) :=
    ((Nat.mod_modEq u G).add (Nat.ModEq.refl v)).trans (Nat.mod_modEq (u + v) G).symm
  have h3 : (u % G + v) % G = (u + v) % G := Nat.mod_eq_of_modEq h' (Nat.mod_lt _ hG)
  exact h1.trans ((congrArg (fun t : Fin G => S t) (Fin.ext h3)).trans h2.symm)

/-- **Cyclic access depends only on the position modulo `G`.** -/
theorem cyc_congr {x y : ℕ} (h : Nat.ModEq G x y) : cyc hG S x = cyc hG S y := by
  have h' : Nat.ModEq G x (y % G) := h.trans (Nat.mod_modEq y G).symm
  have h1 : x % G = y % G := Nat.mod_eq_of_modEq h' (Nat.mod_lt _ hG)
  have h2 : cyc hG S x = S ⟨x % G, Nat.mod_lt _ hG⟩ := rfl
  have h3 : cyc hG S y = S ⟨y % G, Nat.mod_lt _ hG⟩ := rfl
  exact h2.trans ((congrArg (fun t : Fin G => S t) (Fin.ext h1)).trans h3.symm)

/-- **Reading the offset `t` from a start is reading the offset `(t + q) % G`
from the same start stepped back by `q`.**  The index conversion that lets a
full-turn agreement of a backward-extended triple be read back at the
original triple. -/
theorem cyc_offset_shift {q t : ℕ} (hq : q ≤ G) {a : Fin G} :
    cyc hG S (a.val + t) = cyc hG S ((rotAdd hG (G - q) a).val + (t + q) % G) := by
  have hs : (t + q) % G ≡ t + q [MOD G] := Nat.mod_modEq (t + q) G
  have hA : (rotAdd hG (G - q) a).val ≡ a.val + (G - q) [MOD G] :=
    Nat.mod_modEq (a.val + (G - q)) G
  have h1 := hA.add hs
  rw [show a.val + (G - q) + (t + q) = a.val + G + t from by omega] at h1
  have h2 : a.val + G + t ≡ a.val + t [MOD G] := by
    rw [show a.val + G + t = (a.val + t) + G from by omega, Nat.add_comm (a.val + t) G]
    exact Nat.add_modEq_left
  exact cyc_congr hG S (h1.trans h2).symm

/-- **Stepping back by `q` and reading at `t < q` is reading `q - 1 - t`
positions before `x`.**  One of the two index conversions of
`backAgr3F_add`. -/
theorem cyc_shift_left {q t : ℕ} (hq : q ≤ G) (ht : t < q) (x : ℕ) :
    cyc hG S (x + G - 1 - (q - 1 - t)) = cyc hG S ((x + (G - q)) % G + t) := by
  have e : x + (G - q) + t = x + G - 1 - (q - 1 - t) := by omega
  rw [← e, ← cyc_mod_add hG S (x + (G - q)) t]

/-- **Stepping back by `q` and reading at `q ≤ t` is reading `t - q` positions
forward from `x`.**  The other conversion. -/
theorem cyc_shift_right {q t : ℕ} (hq : q ≤ G) (htq : q ≤ t) (x : ℕ) :
    cyc hG S (x + (t - q)) = cyc hG S ((x + (G - q)) % G + t) := by
  have e : x + (t - q) + G = x + (G - q) + t := by omega
  rw [← cyc_add_G hG S (x + (t - q)), e, ← cyc_mod_add hG S (x + (G - q)) t]

/-- **The preceding symbol of the start stepped back by `q` is the symbol `q`
positions before the preceding symbol of the original start.** -/
theorem cyc_preceding_shift {q : ℕ} (hq : q < G) (x : ℕ) :
    cyc hG S (x + G - 1 + (G - q)) = cyc hG S (x + G - 1 - q) := by
  rw [show x + G - 1 + (G - q) = (x + G - 1 - q) + G by omega, cyc_add_G]

/-- **The symbol following the length-`q + m` window at the start stepped
back by `q` is the symbol following the length-`m` window at the original
start.** -/
theorem cyc_following_shift {q m : ℕ} (hq : q ≤ G) (x : ℕ) :
    cyc hG S (x + (q + m) + (G - q)) = cyc hG S (x + m) := by
  rw [show x + (q + m) + (G - q) = (x + m) + G by omega, cyc_add_G]

/-- **A rotation by a fixed amount is injective.** -/
theorem rotAdd_inj {r : ℕ} {x y : Fin G} (h : rotAdd hG r x = rotAdd hG r y) : x = y := by
  have h0 : rotAdd hG (r % G) x = rotAdd hG (r % G) y := by
    rw [rotAdd_mod hG r x] at h
    rw [rotAdd_mod hG r y] at h
    exact h
  have hx : (nextPos hG)^[r % G] x = rotAdd hG (r % G) x := rotAdd_iterate hG (r % G) x
  have hy : (nextPos hG)^[r % G] y = rotAdd hG (r % G) y := rotAdd_iterate hG (r % G) y
  refine ((nextPos_inj hG).iterate (r % G)) ?_
  calc (nextPos hG)^[r % G] x = rotAdd hG (r % G) x := hx
    _ = rotAdd hG (r % G) y := h0
    _ = (nextPos hG)^[r % G] y := hy.symm

/-- **The symbol preceding a start shifted by `r`. -/
theorem preceding_rotAdd (r : ℕ) (a : Fin G) :
    (mkGenome hG S).Preceding (rotAdd hG r a) = cyc hG S (a.val + G - 1 + r) := by
  change cyc hG S ((a.val + r) % G + G - 1) = cyc hG S (a.val + G - 1 + r)
  have e1 : (a.val + r) % G + G - 1 = (a.val + r) % G + (G - 1) := by omega
  have e3 : a.val + r + (G - 1) = a.val + G - 1 + r := by omega
  rw [e1, cyc_mod_add hG S (a.val + r) (G - 1), e3]

/-- **The symbol following a length-`e` window at a start shifted by `r`. -/
theorem following_rotAdd (r e : ℕ) (a : Fin G) :
    (mkGenome hG S).Following e (rotAdd hG r a) = cyc hG S (a.val + e + r) := by
  change cyc hG S ((a.val + r) % G + e) = cyc hG S (a.val + e + r)
  rw [cyc_mod_add hG S (a.val + r) e]
  congr 1
  omega

/-! ## 2. Three occurrences: forward and backward agreement -/

/-- **The three length-`e` windows at `a`, `b`, `c` agree.**  This is
`BBTUniqueEulerian.Agr3` on the same word, repeated here so that the
maximality and combination lemmas below can be stated directly. -/
def Agr3F (hG : 0 < G) (S : Fin G → α) (e : ℕ) (a b c : Fin G) : Prop :=
  ∀ d : Fin e, cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val) ∧
    cyc hG S (a.val + d.val) = cyc hG S (c.val + d.val)

instance (hG : 0 < G) (S : Fin G → α) (e : ℕ) (a b c : Fin G) :
    Decidable (Agr3F hG S e a b c) := by
  unfold Agr3F
  infer_instance

/-- **The three occurrences agree at the `p` positions immediately
preceding them.**  The three-occurrence analogue of
`BBTMaximalExtension.BackAgrees`: `p = 0` is the trivial agreement, `p = 1`
says the three preceding symbols agree. -/
def BackAgr3F (hG : 0 < G) (S : Fin G → α) (p : ℕ) (a b c : Fin G) : Prop :=
  ∀ d : Fin p, cyc hG S (a.val + G - 1 - d.val) = cyc hG S (b.val + G - 1 - d.val) ∧
    cyc hG S (a.val + G - 1 - d.val) = cyc hG S (c.val + G - 1 - d.val)

instance (hG : 0 < G) (S : Fin G → α) (p : ℕ) (a b c : Fin G) :
    Decidable (BackAgr3F hG S p a b c) := by
  unfold BackAgr3F
  infer_instance

/-- Forward agreement, read at arbitrary offsets. -/
theorem agr3F_iff {e : ℕ} {a b c : Fin G} :
    Agr3F hG S e a b c ↔
      ∀ t : ℕ, t < e →
        cyc hG S (a.val + t) = cyc hG S (b.val + t) ∧
          cyc hG S (a.val + t) = cyc hG S (c.val + t) := by
  constructor
  · intro h t ht
    exact h ⟨t, ht⟩
  · intro h d
    exact h d.val d.isLt

/-- Backward agreement, read at arbitrary offsets. -/
theorem backAgr3F_iff {p : ℕ} {a b c : Fin G} :
    BackAgr3F hG S p a b c ↔
      ∀ t : ℕ, t < p →
        cyc hG S (a.val + G - 1 - t) = cyc hG S (b.val + G - 1 - t) ∧
          cyc hG S (a.val + G - 1 - t) = cyc hG S (c.val + G - 1 - t) := by
  constructor
  · intro h t ht
    exact h ⟨t, ht⟩
  · intro h d
    exact h d.val d.isLt

/-- **Forward agreement is downward closed.** -/
theorem agr3F_mono {e e' : ℕ} {a b c : Fin G} (he' : e' ≤ e) (h : Agr3F hG S e a b c) :
    Agr3F hG S e' a b c := by
  intro d
  exact h ⟨d.val, lt_of_lt_of_le d.isLt he'⟩

/-- **Backward agreement is downward closed.** -/
theorem backAgr3F_mono {p p' : ℕ} {a b c : Fin G} (hp' : p' ≤ p)
    (h : BackAgr3F hG S p a b c) : BackAgr3F hG S p' a b c := by
  intro d
  exact h ⟨d.val, lt_of_lt_of_le d.isLt hp'⟩

/-- **One vertex label is a three-occurrence agreement at length `L - 1`.** -/
theorem agr3F_of_vtx {L : ℕ} {a b c : Fin G}
    (h1 : vtx hG L S a = vtx hG L S b) (h2 : vtx hG L S a = vtx hG L S c) :
    Agr3F hG S (L - 1) a b c := by
  intro d
  exact ⟨congrFun h1 d, congrFun h2 d⟩

/-- **A three-occurrence agreement is three pairwise agreements.** -/
theorem agr3F_iff_agree {e : ℕ} {a b c : Fin G} (h : Agr3F hG S e a b c) :
    (mkGenome hG S).Agree e a b ∧ (mkGenome hG S).Agree e a c ∧
      (mkGenome hG S).Agree e b c := by
  have h' : ∀ d : Fin e, cyc hG S (b.val + d.val) = cyc hG S (c.val + d.val) := by
    intro d
    obtain ⟨h1, h2⟩ := h d
    exact h1.symm.trans h2
  refine ⟨?_, ?_, ?_⟩
  · intro d
    exact (h d).1
  · intro d
    exact (h d).2
  · intro d
    exact h' d

/-- **Stepping the three occurrences backwards composes with the forward
agreement.**  If they agree at the `q` positions before them *and* on the `m`
positions from them, then the triple `rotAdd hG (G - q) a`,
`rotAdd hG (G - q) b`, `rotAdd hG (G - q) c` agrees on `q + m` consecutive
positions.  This is the three-occurrence composition that
`docs/bbt-eulerian-cycle-89.md` §6 lists as the missing index arithmetic for
*two* occurrences; at three occurrences it is what produces the maximal
triple repeat of the dichotomy. -/
theorem backAgr3F_add {q m : ℕ} (hq : q ≤ G) {a b c : Fin G}
    (hback : BackAgr3F hG S q a b c) (hfwd : Agr3F hG S m a b c) :
    Agr3F hG S (q + m) (rotAdd hG (G - q) a) (rotAdd hG (G - q) b)
      (rotAdd hG (G - q) c) := by
  have hback' := (backAgr3F_iff hG S (p := q) (a := a) (b := b) (c := c)).mp hback
  have hfwd' := (agr3F_iff hG S (e := m) (a := a) (b := b) (c := c)).mp hfwd
  have hgoal : ∀ t : ℕ, t < q + m →
      cyc hG S ((a.val + (G - q)) % G + t) = cyc hG S ((b.val + (G - q)) % G + t) ∧
        cyc hG S ((a.val + (G - q)) % G + t) = cyc hG S ((c.val + (G - q)) % G + t) := by
    intro t ht
    by_cases hcase : t < q
    · -- inside the backward part: read the triple agreement at `q - 1 - t`
      have hu : q - 1 - t < q := by omega
      obtain ⟨h1, h2⟩ := hback' (q - 1 - t) hu
      have h1s : cyc hG S ((a.val + (G - q)) % G + t)
          = cyc hG S ((b.val + (G - q)) % G + t) := by
        rw [← cyc_shift_left hG S hq hcase a.val, ← cyc_shift_left hG S hq hcase b.val]
        exact h1
      have h2s : cyc hG S ((a.val + (G - q)) % G + t)
          = cyc hG S ((c.val + (G - q)) % G + t) := by
        rw [← cyc_shift_left hG S hq hcase a.val, ← cyc_shift_left hG S hq hcase c.val]
        exact h2
      exact ⟨h1s, h2s⟩
    · -- inside the forward part: read the triple agreement at `t - q`
      have hq' : q ≤ t := by omega
      have h1 : cyc hG S (a.val + (t - q)) = cyc hG S (b.val + (t - q)) :=
        (hfwd' (t - q) (by omega)).1
      have h2 : cyc hG S (a.val + (t - q)) = cyc hG S (c.val + (t - q)) :=
        (hfwd' (t - q) (by omega)).2
      have h1s : cyc hG S ((a.val + (G - q)) % G + t)
          = cyc hG S ((b.val + (G - q)) % G + t) := by
        rw [← cyc_shift_right hG S hq hq' a.val, ← cyc_shift_right hG S hq hq' b.val]
        exact h1
      have h2s : cyc hG S ((a.val + (G - q)) % G + t)
          = cyc hG S ((c.val + (G - q)) % G + t) := by
        rw [← cyc_shift_right hG S hq hq' a.val, ← cyc_shift_right hG S hq hq' c.val]
        exact h2
      exact ⟨h1s, h2s⟩
  exact (agr3F_iff hG S (e := q + m) (a := rotAdd hG (G - q) a) (b := rotAdd hG (G - q) b)
    (c := rotAdd hG (G - q) c)).mpr hgoal

/-! ## 3. The two maximal extensions, at three occurrences -/

/-- **The forward agreement lengths of three occurrences, up to a full
turn.** -/
def agr3FSet (hG : 0 < G) (S : Fin G → α) (a b c : Fin G) : Finset ℕ :=
  (Finset.range (G + 1)).filter (fun e => Agr3F hG S e a b c)

/-- **The backward agreement lengths of three occurrences, up to a full
turn.** -/
def backAgr3FSet (hG : 0 < G) (S : Fin G → α) (a b c : Fin G) : Finset ℕ :=
  (Finset.range (G + 1)).filter (fun p => BackAgr3F hG S p a b c)

/-- **The maximal forward agreement of three occurrences.**  `m ≥ e₀`,
`m ≤ G`, `m` is an agreement length, and if `m < G` the agreement stops
there.  The `m = G` case is the *periodic* case, and it is exactly the case
in which the three occurrences collapse modulo the least period (§4). -/
theorem max_agr3F {a b c : Fin G} {e₀ : ℕ} (he₀ : e₀ ≤ G) (hag0 : Agr3F hG S e₀ a b c) :
    ∃ m : ℕ, e₀ ≤ m ∧ m ≤ G ∧ Agr3F hG S m a b c ∧
      (m < G → ¬ Agr3F hG S (m + 1) a b c) := by
  set T := agr3FSet hG S a b c with hT
  have hmem0 : e₀ ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hag0⟩
  have hne : T.Nonempty := ⟨e₀, hmem0⟩
  have hagm : Agr3F hG S (T.max' hne) a b c :=
    (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  have hleG : T.max' hne ≤ G := by
    have h1 := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.max'_mem _ hne)).1
    omega
  refine ⟨T.max' hne, Finset.le_max' _ e₀ hmem0, hleG, hagm, ?_⟩
  intro hlt h
  have hmem1 : T.max' hne + 1 ∈ T :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩
  have hle := Finset.le_max' T _ hmem1
  rw [show T.max' ⟨_, hmem1⟩ = T.max' hne from rfl] at hle
  omega

/-- **The maximal backward agreement of three occurrences.**  `q ≤ G`,
`q` is a backward agreement length, and if `q < G` the backward agreement
stops there.  `q = G` is the periodic case. -/
theorem max_backAgr3F (a b c : Fin G) :
    ∃ q : ℕ, q ≤ G ∧ BackAgr3F hG S q a b c ∧
      (q < G → ¬ BackAgr3F hG S (q + 1) a b c) := by
  set T := backAgr3FSet hG S a b c with hT
  have hzero : 0 ∈ T := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    intro d
    exact Fin.elim0 d
  have hne : T.Nonempty := ⟨0, hzero⟩
  have hq0 : BackAgr3F hG S (T.max' hne) a b c :=
    (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  have hleG : T.max' hne ≤ G := by
    have h1 := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.max'_mem _ hne)).1
    omega
  refine ⟨T.max' hne, hleG, hq0, ?_⟩
  intro hlt h
  have hmem1 : T.max' hne + 1 ∈ T :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩
  have hle := Finset.le_max' T _ hmem1
  rw [show T.max' ⟨_, hmem1⟩ = T.max' hne from rfl] at hle
  omega

/-- **At a maximal forward agreement, the three following symbols are not all
equal.**  This is `BBTMaximalExtension`'s "maximality forces the following
symbols to differ", for three occurrences. -/
theorem following_ne_of_max_agr3F {a b c : Fin G} {m : ℕ} (hm : m < G)
    (hag : Agr3F hG S m a b c) (hnot : ¬ Agr3F hG S (m + 1) a b c) :
    ¬ (cyc hG S (a.val + m) = cyc hG S (b.val + m) ∧
        cyc hG S (a.val + m) = cyc hG S (c.val + m)) := by
  intro h
  apply hnot
  intro d
  by_cases hd : d.val < m
  · exact hag ⟨d.val, hd⟩
  · have hd' : d.val = m := by omega
    rw [hd']
    exact h

/-- **At a maximal backward agreement, the three preceding symbols are not all
equal.** -/
theorem preceding_ne_of_max_backAgr3F {a b c : Fin G} {q : ℕ} (hq : q < G)
    (hag : BackAgr3F hG S q a b c) (hnot : ¬ BackAgr3F hG S (q + 1) a b c) :
    ¬ (cyc hG S (a.val + G - 1 - q) = cyc hG S (b.val + G - 1 - q) ∧
        cyc hG S (a.val + G - 1 - q) = cyc hG S (c.val + G - 1 - q)) := by
  intro h
  apply hnot
  intro d
  by_cases hd : d.val < q
  · exact hag ⟨d.val, hd⟩
  · have hd' : d.val = q := by omega
    rw [hd']
    exact h

/-! ## 4. The periodic alternative: agreement for a full turn -/

/-- **Three occurrences agreeing for a full turn make the shift a period.**
This is `BBTUniqueEulerian.period_of_agree_all`, read on two of the three
pairs. -/
theorem period_of_agr3F {a b c : Fin G} (h : Agr3F hG S G a b c) :
    Period hG S (sh hG a b) := by
  refine period_of_agree_all hG S (a := a) (b := b) ?_
  intro d
  exact (h d).1

/-- **Three occurrences agreeing at every position before them agree for a
full turn.**  `q = G` is the periodic case of the backward extension. -/
theorem agr3F_G_of_backAgr3F {a b c : Fin G} (h : BackAgr3F hG S G a b c) :
    Agr3F hG S G a b c := by
  have h' := (backAgr3F_iff hG S (p := G) (a := a) (b := b) (c := c)).mp h
  rw [agr3F_iff]
  intro t ht
  obtain ⟨h1, h2⟩ := h' (G - 1 - t) (by omega)
  have ea : a.val + G - 1 - (G - 1 - t) = a.val + t := by omega
  have eb : b.val + G - 1 - (G - 1 - t) = b.val + t := by omega
  have ec : c.val + G - 1 - (G - 1 - t) = c.val + t := by omega
  rw [ea, eb] at h1
  rw [ea, ec] at h2
  exact ⟨h1, h2⟩

/-- **A full-turn agreement survives being read back before a common
backward step.**  If the triple stepped back by `q` agrees for a full turn,
then the original triple does too --- a full turn of positions is a full turn
of the circle whichever window of `G` consecutive positions one reads it
from.  This is what transports the periodic alternative of
`three_occurrences_collapse_or_tripleRepeat` back from the backward-extended
triple to the original occurrences, i.e. it plays the role of a
"shift-congruence for `sh`" without any `sh` arithmetic. -/
theorem agr3F_G_of_shifted {q : ℕ} (hq : q ≤ G) {a b c : Fin G}
    (h : Agr3F hG S G (rotAdd hG (G - q) a) (rotAdd hG (G - q) b) (rotAdd hG (G - q) c)) :
    Agr3F hG S G a b c := by
  have h' := (agr3F_iff hG S (e := G) (a := rotAdd hG (G - q) a) (b := rotAdd hG (G - q) b)
    (c := rotAdd hG (G - q) c)).mp h
  rw [agr3F_iff]
  intro t ht
  have h1 := cyc_offset_shift hG S hq (a := a) (t := t)
  have h2 := cyc_offset_shift hG S hq (a := b) (t := t)
  have h3 := cyc_offset_shift hG S hq (a := c) (t := t)
  obtain ⟨hb, hc⟩ := h' ((t + q) % G) (Nat.mod_lt _ hG)
  rw [← h1, ← h2] at hb
  rw [← h1, ← h3] at hc
  exact ⟨hb, hc⟩

/-- **The least period divides the shift of a full-turn agreement.** -/
theorem leastPeriod_dvd_of_agr3F {a b c : Fin G} (h : Agr3F hG S G a b c) :
    leastPeriod hG S ∣ sh hG a b :=
  leastPeriod_dvd_period hG S (Nat.le_of_lt (sh_lt hG a b)) (period_of_agr3F hG S h)

/-- **The least period divides the shift of a full-turn backward
agreement.** -/
theorem leastPeriod_dvd_of_backAgr3F {a b c : Fin G} (h : BackAgr3F hG S G a b c) :
    leastPeriod hG S ∣ sh hG a b :=
  leastPeriod_dvd_of_agr3F hG S (agr3F_G_of_backAgr3F hG S (a := a) (b := b) (c := c) h)

/-! ## 5. The fibre/period lemma -/

/-- **The fibre/period lemma.**  Three pairwise distinct starts carrying one
and the same `(L-1)`-mer either collapse modulo the least period, or the
three occurrences --- extended backwards as far as they agree --- carry a
**maximal triple repeat** of length `≥ L - 1`.

The second alternative is a `LongObstruction` (`BBTMaximalExtension.triple_disjunct`),
so an `Ukkonen` word has only the first alternative
(`three_occurrences_collapse_of_Ukkonen` below).

No primitivity is used, and no assumption on the interleaved clause of
`Ukkonen`.  The proof is the two maximal extensions of
`BBTMaximalExtension` §2/§3a, read at three occurrences, together with the
period arithmetic of `BBTUniqueEulerian` §1.1. -/
theorem three_occurrences_collapse_or_tripleRepeat {L : ℕ} (hL : 2 ≤ L)
    {a b c : Fin G} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hv1 : vtx hG L S a = vtx hG L S b) (hv2 : vtx hG L S a = vtx hG L S c) :
    leastPeriod hG S ∣ sh hG a b ∨ leastPeriod hG S ∣ sh hG a c ∨
      leastPeriod hG S ∣ sh hG b c
      ∨ ∃ q m : ℕ, ∃ e : Fin G,
          (mkGenome hG S).IsTripleRepeat e (rotAdd hG (G - q) a)
            (rotAdd hG (G - q) b) (rotAdd hG (G - q) c) ∧ L - 1 ≤ e.val := by
  have hℓ1 : 1 ≤ L - 1 := by omega
  -- the three occurrences agree at length `L - 1`
  have hag0 : Agr3F hG S (L - 1) a b c := agr3F_of_vtx hG S hv1 hv2
  by_cases hbig : G ≤ L - 1
  · -- the label is at least a full turn long: the three agree for a full turn
    exact Or.inl (leastPeriod_dvd_of_agr3F (α := α) hG S (a := a) (b := b) (c := c)
      (agr3F_mono (α := α) hG S (by omega) hag0))
  -- the two maximal extensions
  obtain ⟨m, hme, hmG, hagm, hmnot⟩ :=
    max_agr3F (α := α) hG S (by omega) hag0
  obtain ⟨q, hqG, hbq, hbqnot⟩ := max_backAgr3F (α := α) hG S a b c
  -- the backward step, composing the two extensions
  have hN : Agr3F hG S (q + m) (rotAdd hG (G - q) a) (rotAdd hG (G - q) b)
      (rotAdd hG (G - q) c) :=
    backAgr3F_add (α := α) hG S (a := a) (b := b) (c := c) hqG hbq hagm
  by_cases hcase : m = G
  · -- full turn forward: the shift `sh a b` is a period
    exact Or.inl (leastPeriod_dvd_of_agr3F (α := α) hG S (a := a) (b := b) (c := c)
      (by simpa only [hcase] using hagm))
  by_cases hcase2 : q = G
  · -- full turn backward: the same, read backwards
    exact Or.inl (leastPeriod_dvd_of_backAgr3F (α := α) hG S (a := a) (b := b) (c := c)
      (by simpa only [hcase2] using hbq))
  by_cases hcase3 : G ≤ q + m
  · -- the composed agreement covers a full turn: transport the period back
    refine Or.inl ?_
    have ha' : Agr3F hG S G (rotAdd hG (G - q) a) (rotAdd hG (G - q) b)
        (rotAdd hG (G - q) c) := agr3F_mono (α := α) hG S (by omega) hN
    have hper : Period hG S (sh hG a b) :=
      period_of_agr3F (α := α) hG S (a := a) (b := b) (c := c)
        (agr3F_G_of_shifted (α := α) hG S hqG ha')
    exact leastPeriod_dvd_period hG S (Nat.le_of_lt (sh_lt hG a b)) hper
  · -- the composed triple is a maximal triple repeat of length `q + m < G`
    have hNFin : q + m < G := by omega
    refine Or.inr (Or.inr (Or.inr ⟨q, m, ⟨q + m, hNFin⟩, ?_,
      le_trans hme (Nat.le_add_left m q)⟩))
    obtain ⟨hAg1, hAg2, hAg3⟩ := agr3F_iff_agree hG S hN
    have hab' : rotAdd hG (G - q) a ≠ rotAdd hG (G - q) b := by
      intro he
      exact hab (rotAdd_inj hG he)
    have hac' : rotAdd hG (G - q) a ≠ rotAdd hG (G - q) c := by
      intro he
      exact hac (rotAdd_inj hG he)
    have hbc' : rotAdd hG (G - q) b ≠ rotAdd hG (G - q) c := by
      intro he
      exact hbc (rotAdd_inj hG he)
    have hprec := preceding_ne_of_max_backAgr3F (α := α) hG S (a := a) (b := b) (c := c)
      (by omega) hbq (hbqnot (by omega))
    have hfoll := following_ne_of_max_agr3F (α := α) hG S (a := a) (b := b) (c := c)
      (by omega) hagm (hmnot (by omega))
    -- the maximal backward step lands the preceding symbols on the maximal
    -- backward point of the original triple
    have hqlt : q < G := by omega
    have hprec' : ¬ ((mkGenome hG S).Preceding (rotAdd hG (G - q) a)
          = (mkGenome hG S).Preceding (rotAdd hG (G - q) b) ∧
        (mkGenome hG S).Preceding (rotAdd hG (G - q) b)
          = (mkGenome hG S).Preceding (rotAdd hG (G - q) c)) := by
      intro h
      have hp1 : cyc hG S (a.val + G - 1 - q) = cyc hG S (b.val + G - 1 - q) := by
        have e1 := preceding_rotAdd hG S (G - q) a
        have e2 := preceding_rotAdd hG S (G - q) b
        have e3 := cyc_preceding_shift hG S hqlt a.val
        have e4 := cyc_preceding_shift hG S hqlt b.val
        rw [e1, e2, e3, e4] at h
        exact h.1
      have hp2 : cyc hG S (b.val + G - 1 - q) = cyc hG S (c.val + G - 1 - q) := by
        have e2 := preceding_rotAdd hG S (G - q) b
        have e3 := preceding_rotAdd hG S (G - q) c
        have e4 := cyc_preceding_shift hG S hqlt b.val
        have e5 := cyc_preceding_shift hG S hqlt c.val
        rw [e2, e3, e4, e5] at h
        exact h.2
      exact hprec ⟨hp1, hp1.trans hp2⟩
    -- the maximal forward step lands the following symbols on the maximal
    -- forward point of the original triple
    have hfoll' : ¬ ((mkGenome hG S).Following (q + m) (rotAdd hG (G - q) a)
          = (mkGenome hG S).Following (q + m) (rotAdd hG (G - q) b) ∧
        (mkGenome hG S).Following (q + m) (rotAdd hG (G - q) b)
          = (mkGenome hG S).Following (q + m) (rotAdd hG (G - q) c)) := by
      intro h
      have hf1 : cyc hG S (a.val + m) = cyc hG S (b.val + m) := by
        have e1 := following_rotAdd hG S (G - q) (q + m) a
        have e2 := following_rotAdd hG S (G - q) (q + m) b
        have e3 := cyc_following_shift hG S hqG (m := m) a.val
        have e4 := cyc_following_shift hG S hqG (m := m) b.val
        rw [e1, e2, e3, e4] at h
        exact h.1
      have hf2 : cyc hG S (b.val + m) = cyc hG S (c.val + m) := by
        have e2 := following_rotAdd hG S (G - q) (q + m) b
        have e3 := following_rotAdd hG S (G - q) (q + m) c
        have e4 := cyc_following_shift hG S hqG (m := m) b.val
        have e5 := cyc_following_shift hG S hqG (m := m) c.val
        rw [e2, e3, e4, e5] at h
        exact h.2
      exact hfoll ⟨hf1, hf1.trans hf2⟩
    exact ⟨le_trans hℓ1 (le_trans hme (Nat.le_add_left m q)), hNFin, hab', hac', hbc',
      hAg1, hAg2, hAg3, hprec', hfoll'⟩

/-- **Under `Ukkonen`, three occurrences of one `(L-1)`-mer collapse modulo
the least period.**  This is the fibre/period statement proper: an `Ukkonen`
word has no maximal triple repeat of length `≥ L - 1`, so the second
alternative of `three_occurrences_collapse_or_tripleRepeat` is a
`LongObstruction` and is excluded. -/
theorem three_occurrences_collapse_of_Ukkonen {L : ℕ} (hL : 2 ≤ L)
    (hU : Ukkonen hG L S) {a b c : Fin G} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hv1 : vtx hG L S a = vtx hG L S b) (hv2 : vtx hG L S a = vtx hG L S c) :
    leastPeriod hG S ∣ sh hG a b ∨ leastPeriod hG S ∣ sh hG a c ∨
      leastPeriod hG S ∣ sh hG b c := by
  rcases three_occurrences_collapse_or_tripleRepeat (α := α) hG S hL hab hac hbc hv1 hv2
    with h1 | h2 | h3 | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)
  · obtain ⟨q, m, e, ht, hlen⟩ := h4
    exact absurd
      (hU.1 e (rotAdd hG (G - q) a) (rotAdd hG (G - q) b) (rotAdd hG (G - q) c) ht)
      (by omega)

/-! ## 6. Period classes, and the fibres of the vertex labelling -/

/-- **A period class**: the starts congruent to `a` modulo the least period,
i.e. the realisations of one label that are indistinguishable from `a` by
periodicity alone.  `BBTUniqueEulerian.vtx_eq_of_sh` says the class is
carried by one vertex. -/
noncomputable def classOf (hG : 0 < G) (S : Fin G → α) (a : Fin G) : Finset (Fin G) :=
  Finset.univ.filter (fun x => leastPeriod hG S ∣ sh hG a x)

noncomputable instance (hG : 0 < G) (S : Fin G → α) (a : Fin G) :
    DecidablePred fun x : Fin G => leastPeriod hG S ∣ sh hG a x :=
  fun _ => inferInstance

theorem mem_classOf {a x : Fin G} :
    x ∈ classOf hG S a ↔ leastPeriod hG S ∣ sh hG a x := by
  unfold classOf
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩

/-- **Congruence modulo the least period is transitive**, so the classes
partition the starts. -/
theorem sameClass_trans {p : ℕ} (hpG : p ∣ G) {x y z : Fin G}
    (h1 : p ∣ sh hG x y) (h2 : p ∣ sh hG y z) : p ∣ sh hG x z :=
  sh_dvd_trans hG hpG h1 h2

/-- **A period class is carried by one vertex.** -/
theorem mem_fibre_of_mem_classOf {L : ℕ} {a x : Fin G}
    (h : x ∈ classOf hG S a) :
    vtx hG L S x = vtx hG L S a := by
  exact (vtx_eq_of_sh hG S (leastPeriod_spec hG S).1
    ((mem_classOf hG S (a := a) (x := x)).mp h)).symm

/-- **The class of `a` lies in the fibre of `vtx a`.** -/
theorem classOf_subset_fibre {L : ℕ} {a : Fin G} :
    classOf hG S a ⊆ fibre hG L S (vtx hG L S a) := by
  intro x hx
  rw [mem_fibre hG L S]
  exact mem_fibre_of_mem_classOf hG S hx

/-- **A period is a shift invariance.**  This is the bridge between the
period arithmetic of `BBTUniqueEulerian` and the primality interface of
`RepeatAdapter`, which is stated in terms of `ShiftInvariant`. -/
theorem shiftInvariant_of_period {s : ℕ} (hs : Period hG S s) :
    ShiftInvariant hG S s := by
  intro i
  have key : cyc hG S (i + s) = S (rotAdd hG s ⟨i % G, Nat.mod_lt _ hG⟩) := by
    calc cyc hG S (i + s) = S ⟨(i + s) % G, Nat.mod_lt _ hG⟩ := rfl
      _ = S ⟨(i % G + s) % G, Nat.mod_lt _ hG⟩ :=
        congrArg (fun t : Fin G => S t) (Fin.ext (mod_add_shl i s))
      _ = S (rotAdd hG s ⟨i % G, Nat.mod_lt _ hG⟩) := rfl
  calc cyc hG S i = S ⟨i % G, Nat.mod_lt _ hG⟩ := rfl.symm
    _ = S (rotAdd hG s ⟨i % G, Nat.mod_lt _ hG⟩) := (hs ⟨i % G, Nat.mod_lt _ hG⟩).symm
    _ = cyc hG S (i + s) := key.symm

/-- **Primitivity of the truth means the least period is `G`.** -/
theorem leastPeriod_eq_G_of_primitive (hprim : IsPrimitive hG S) :
    leastPeriod hG S = G := by
  have hspec := leastPeriod_spec hG S
  have hpos : 0 < leastPeriod hG S := hspec.2.1
  by_contra hne
  have hlt : leastPeriod hG S < G := by omega
  exact hprim (leastPeriod hG S) hpos hlt (shiftInvariant_of_period hG S hspec.1)

/-- **Congruence modulo `G` is equality.** -/
theorem sh_eq_zero_of_dvd_G {a b : Fin G} (h : G ∣ sh hG a b) : a = b := by
  have hz : sh hG a b = 0 := by
    rcases h with ⟨c, hc⟩
    have hlt := sh_lt hG a b
    have hcz : c = 0 := by
      by_contra hc0
      have h1 : 1 ≤ c := by omega
      have h2 : G ≤ G * c := by
        have := Nat.mul_le_mul_left h1 (k := G)
        simpa using this
      omega
    rw [hcz, Nat.mul_zero] at hc
    exact hc
  have h' : rotAdd hG 0 a = b := by
    rw [← hz]
    exact rotAdd_sh hG a b
  rw [rotAdd_zero hG a] at h'
  exact h'

/-- **Congruence modulo the least period, at its least period `G`, is
equality.** -/
theorem sh_eq_zero_of_dvd_leastPeriod {a b : Fin G}
    (h : leastPeriod hG S ∣ sh hG a b) (heq : leastPeriod hG S = G) : a = b := by
  have hz : sh hG a b = 0 := by
    rcases h with ⟨c, hc⟩
    have hlt := sh_lt hG a b
    rw [heq] at hc
    have hcz : c = 0 := by
      by_contra hc0
      have h1 : 1 ≤ c := by omega
      have h2 : G ≤ G * c := by
        have := Nat.mul_le_mul_left h1 (k := G)
        simpa using this
      omega
    rw [hcz, Nat.mul_zero] at hc
    exact hc
  have h' : rotAdd hG 0 a = b := by
    rw [← hz]
    exact rotAdd_sh hG a b
  rw [rotAdd_zero hG a] at h'
  exact h'

/-- **The shift of a start to itself is zero.** -/
theorem sh_self (a : Fin G) : sh hG a a = 0 := by
  have h := rotAdd_sh hG a a
  have hfin : (⟨sh hG a a, sh_lt hG a a⟩ : Fin G) = ⟨0, hG⟩ :=
    rotAdd_inj_lt hG (n := ⟨sh hG a a, sh_lt hG a a⟩) (n' := ⟨0, hG⟩) (x := a)
      (by rw [h, rotAdd_zero hG a])
  exact congrArg Fin.val hfin

/-- **Every start is in its own class.** -/
theorem dvd_sh_self (a : Fin G) : leastPeriod hG S ∣ sh hG a a := by
  rw [sh_self hG a]
  exact Nat.dvd_zero (leastPeriod hG S)

/-- **A start lies in the class of any start equal to it.** -/
theorem dvd_sh_of_eq {a b : Fin G} (h : a = b) : leastPeriod hG S ∣ sh hG a b := by
  rw [h]
  exact dvd_sh_self hG S b

/-- **The primitive case: every class is a single start.** -/
theorem classOf_singleton {a : Fin G} (h : leastPeriod hG S = G) :
    classOf hG S a = {a} := by
  ext x
  rw [mem_classOf, Finset.mem_singleton]
  constructor
  · intro hx
    exact (sh_eq_zero_of_dvd_leastPeriod (a := a) (b := x) hG S hx h).symm
  · intro hxa
    rw [hxa]
    exact dvd_sh_self hG S a

/-- **Under `Ukkonen`, the fibre of a branch vertex is carried by at most two
period classes.**  This is the fibre/period bound in the form the
Eulerian-cycle step consumes: an alternative traversal of the condensed
multigraph can differ from the truth's only at branch vertices, and the
occurrences of one vertex live in at most two congruence classes of starts,
so the whole freedom of an alternative traversal is carried by at most two
classes per vertex.

The argument is `three_occurrences_collapse_of_Ukkonen` read on the fibre:
three occurrences of one label cannot be pairwise incongruent, so the
occurrences split into "congruent to `a`" and "the rest", and the rest is
one single class. -/
theorem fibre_subset_two_classes {L : ℕ} (hL : 2 ≤ L) (hU : Ukkonen hG L S)
    {v : Fin (L - 1) → α} (hne : (fibre hG L S v).Nonempty) :
    ∃ a b : Fin G, ∀ x ∈ fibre hG L S v, x ∈ classOf hG S a ∨ x ∈ classOf hG S b := by
  classical
  set F := fibre hG L S v with hF
  obtain ⟨a, ha⟩ := hne
  have hva : vtx hG L S a = v := (mem_fibre hG L S).mp ha
  set B := F.filter (fun y : Fin G => ¬ leastPeriod hG S ∣ sh hG a y) with hB
  by_cases hBne : B.Nonempty
  · obtain ⟨b, hb⟩ := hBne
    have hbf : b ∈ F := (Finset.mem_filter.mp hb).1
    have hvb : vtx hG L S b = v := (mem_fibre hG L S).mp hbf
    have hba : ¬ leastPeriod hG S ∣ sh hG a b := (Finset.mem_filter.mp hb).2
    refine ⟨a, b, fun x hx => ?_⟩
    by_cases hxa : leastPeriod hG S ∣ sh hG a x
    · exact Or.inl ((mem_classOf hG S (a := a) (x := x)).mpr hxa)
    · have hxb : leastPeriod hG S ∣ sh hG b x := by
        by_contra hcon
        have habx : a ≠ x := by
          intro he
          exact hxa (dvd_sh_of_eq hG S he)
        have hax : a ≠ b := by
          intro he
          exact hba (dvd_sh_of_eq hG S he)
        have hbx : b ≠ x := by
          intro he
          exact hcon (dvd_sh_of_eq hG S he)
        rcases three_occurrences_collapse_of_Ukkonen (α := α) hG S hL hU hax habx hbx
          (hva.trans hvb.symm) (hva.trans ((mem_fibre hG L S).mp hx).symm) with h1 | h2 | h3
        · exact absurd h1 hba
        · exact absurd h2 hxa
        · exact absurd h3 hcon
      exact Or.inr ((mem_classOf hG S (a := b) (x := x)).mpr hxb)
  · refine ⟨a, a, fun x hx => Or.inl ?_⟩
    by_contra hcon
    refine hBne ⟨x, ?_⟩
    rw [hB, Finset.mem_filter]
    exact ⟨hx, fun hxa => hcon ((mem_classOf hG S (a := a) (x := x)).mpr hxa)⟩

/-- **The primitive case: every fibre of the vertex labelling has at most two
starts.**  This is the bound the `EulerianCycleGap` step needs at a branch
vertex in the primitive stratum: an `Ukkonen` word that is not a proper power
labels each `(L-1)`-mer at at most two of its `G` starts. -/
theorem fibre_card_le_two_of_primitive {L : ℕ} (hL : 2 ≤ L)
    (hU : Ukkonen hG L S) (hprim : IsPrimitive hG S) (v : Fin (L - 1) → α) :
    (fibre hG L S v).card ≤ 2 := by
  by_cases hne : (fibre hG L S v).Nonempty
  · obtain ⟨a, b, hab⟩ := fibre_subset_two_classes hG S hL hU hne
    have h1 : classOf hG S a = {a} :=
      classOf_singleton hG S (leastPeriod_eq_G_of_primitive hG S hprim)
    have h2 : classOf hG S b = {b} :=
      classOf_singleton hG S (leastPeriod_eq_G_of_primitive hG S hprim)
    have hsub : fibre hG L S v ⊆ insert b ({a} : Finset (Fin G)) := by
      intro x hx
      rcases hab x hx with h | h
      · rw [h1] at h
        exact Finset.mem_insert_of_mem h
      · rw [h2] at h
        show x ∈ insert b ({a} : Finset (Fin G))
        rw [Finset.mem_singleton] at h
        rw [h]
        exact Finset.mem_insert_self b ({a} : Finset (Fin G))
    calc (fibre hG L S v).card ≤ (insert b ({a} : Finset (Fin G))).card :=
        Finset.card_le_card hsub
      _ ≤ (({a} : Finset (Fin G))).card + 1 := Finset.card_insert_le b _
  · have hempty : fibre hG L S v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp

end AssemblyP1.BBTEulerian
