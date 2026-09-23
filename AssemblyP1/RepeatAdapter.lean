import AssemblyP1.OrientedRigidity

/-!
# Repeat-theory adapter (issue #71): primitive and periodic routes to rigidity

This file is the repeat-theory / `I_s` multiplicity-bound adapter that feeds the
`WordLayer.rigidity_same_spectrum` bridge
(`AssemblyP1.OrientedRigidity.rigidity_same_spectrum`) and the parallel
simple-cycle route. It reuses the `WordLayer` definitions (`cyc`, `window`,
`nodeWindow`, `nodeCount`, `genomeNodes`, `support`, `specCount`,
`winPrefix`, `winSuffix`, `Balanced`, `StronglyConnected`, `Reachable`) and
introduces no competing word layer.

## The two branches (no global multiplicity theorem)

Following `docs/source-notes/oriented-se62-rigidity-theorem.md` §3, the
argument splits on primitivity. There is deliberately **no** global
"`I_s` implies every `(L-1)`-window occurs at most twice" theorem: the
periodic case needs a different conclusion (a directed-cycle description),
since a `k`-fold periodic truth has every window multiplicity `k`.

* **Primitive branch** (`primitive_nodeCount_le_two`, Lemma B of the note):
  a primitive circular word with no long Bresler triple repeat has every
  `(L-1)`-window multiplicity `≤ 2`. The corollary
  `primitive_rigidity_same_spectrum` feeds this cap into
  `rigidity_same_spectrum`.
* **Periodic branch** (`periodic_factor_distinct`,
  `unique_circulation_of_cycle`, `periodic_cycle_shape`,
  `periodic_rigidity_same_spectrum`): minimal period plus no long triple
  repeat gives distinctness of the period's length-`(L-1)` factors (Lemma C
  of the note, via the shared extension engine with a small-period
  escape), hence the simple directed-cycle support, on which every
  positive balanced circulation of total `G` is uniquely determined.

## Explicit external interfaces (not kernel-checked here)

* `I_s → NoLongTripleRepeat` (note §3, Fact D: a length-`L` read bridges a
  repeat copy only if its length is `≤ L - 2`, so a read realization in
  `I_s` forbids Bresler triple repeats of length `≥ L - 1`). The full
  read-realization machinery would dominate this packet, so
  `HasLongTripleRepeat` is the interface hypothesis and the implication
  from `I_s` stays documented/external. (Lemma C, by contrast, is now
  kernel-checked as `periodic_factor_distinct`.)
* As in issue #69, the complete-spectrum (BBT) input — same support,
  positivity, balance, total mass of the competitor — remains an external
  hypothesis (`hBsup`, `hBbal`, `hBtot`).

## What is proved in Lean

* `not_primitive_of_ge_G_agree`: triple agreement on `≥ G` consecutive
  positions between distinct residues makes the word shift-invariant.
* `small_period_of_ge_p_agree`: pair agreement on `≥ p` positions
  between mod-`p`-distinct residues forces a strictly smaller period.
* `extend_triple`: shared two-sided maximal-extension engine driving
  both Lemma B and Lemma C (caller-supplied escape for long totals).
* `primitive_nodeCount_le_two`: primitive + no long triple repeat gives
  the `(L-1)`-window cap `nodeCount k ≤ 2` (via the engine with a
  non-primitivity escape).
* `primitive_rigidity_same_spectrum`: the primitive route end-to-end.
* `periodic_factor_distinct`: minimal period + no long triple repeat
  gives distinctness of the period's length-`(L-1)` factors (Lemma C, via
  the engine with a small-period escape; needs `2 ≤ L`).
* `unique_circulation_of_cycle`: abstract positive-circulation uniqueness
  on a simple directed-cycle support (needs strong connectivity: a
  disjoint union of cycles admits distinct constants per component).
* `periodic_cycle_shape`: periodicity + distinct period node windows give
  the simple-cycle shape (`IsSimpleCycle`).
* `periodic_rigidity_same_spectrum`: the periodic route end-to-end,
  consuming the derived `periodic_factor_distinct`.
-/

namespace AssemblyP1.RepeatAdapter

open Finset
open BigOperators

/-! ## Primitive-branch interface: periods, triple repeats -/

/-- Shift-invariance of the circular word by `s`: every position agrees
with the position `s` steps ahead. Its negation below `G` is primitivity. -/
def ShiftInvariant {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (s : ℕ) : Prop :=
  ∀ i : ℕ, OrientedRigidity.cyc hG S i = OrientedRigidity.cyc hG S (i + s)

/-- Primitivity: no nonzero shift below `G` preserves the circular word
(note §3, Lemma B hypothesis: minimal period `G`). -/
def IsPrimitive {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α) : Prop :=
  ∀ s : ℕ, 0 < s → s < G → ¬ ShiftInvariant hG S s

/-- Triple agreement: three (unrestricted-nat) starts whose length-`ℓ`
windows coincide. Starts are `ℕ` so uniform shifts never need side
conditions; residues are compared via `% G`. -/
def TripleAgree {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (a b c ℓ : ℕ) : Prop :=
  ∀ d : ℕ, d < ℓ →
    OrientedRigidity.cyc hG S (a + d) = OrientedRigidity.cyc hG S (b + d) ∧
      OrientedRigidity.cyc hG S (b + d) = OrientedRigidity.cyc hG S (c + d)

/-- Bresler three-copy maximality at starts `a b c` and length `ℓ`
(Bresler et al. 2013, via the rigidity note §1): the three preceding
symbols (position `start + G - 1`, i.e. one step back mod `G`) are not
all equal, and the three following symbols are not all equal. -/
def IsMaximalTriple {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (a b c ℓ : ℕ) : Prop :=
  TripleAgree hG S a b c ℓ ∧
    ¬ (OrientedRigidity.cyc hG S (a + G - 1) =
          OrientedRigidity.cyc hG S (b + G - 1) ∧
        OrientedRigidity.cyc hG S (b + G - 1) =
          OrientedRigidity.cyc hG S (c + G - 1)) ∧
    ¬ (OrientedRigidity.cyc hG S (a + ℓ) =
          OrientedRigidity.cyc hG S (b + ℓ) ∧
        OrientedRigidity.cyc hG S (b + ℓ) =
          OrientedRigidity.cyc hG S (c + ℓ))

/-- A long Bresler triple repeat: three distinct residues carrying a
maximal common window of length `ℓ ≥ L - 1` (note §3, Fact D target).
`¬ HasLongTripleRepeat` is the interface hypothesis implied by `I_s`
(Fact D, external: bridging forbids exactly these). -/
def HasLongTripleRepeat {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (L : ℕ) : Prop :=
  ∃ a b c ℓ : ℕ, L - 1 ≤ ℓ ∧ ℓ < G ∧
    a % G ≠ b % G ∧ b % G ≠ c % G ∧ a % G ≠ c % G ∧
    IsMaximalTriple hG S a b c ℓ

/-- A period of the circular word. -/
def IsPeriod {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (p : ℕ) : Prop :=
  ∀ i : ℕ, OrientedRigidity.cyc hG S i = OrientedRigidity.cyc hG S (i + p)

/-- Minimal-period data for the periodic branch (note §3, Lemma C
hypothesis shape): `p` is a period, `p < G`, `p ∣ G`, and nothing
smaller is a period. The Lean periodic route additionally takes the
Lemma-C distinctness consequence as an explicit hypothesis. -/
def HasMinimalPeriod {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (p : ℕ) : Prop :=
  0 < p ∧ p < G ∧ G % p = 0 ∧ IsPeriod hG S p ∧
    (∀ q : ℕ, 0 < q → q < p → ¬ IsPeriod hG S q)

/-- Simple directed-cycle shape of the window support: every
`(L-1)`-window node has exactly one outgoing and exactly one incoming
length-`L` window edge. This is the word-level cycle interface fed to
`unique_circulation_of_cycle`. -/
def IsSimpleCycle {α : Type} [DecidableEq α] {G : ℕ} (L : ℕ) (hG : 0 < G)
    (S : Fin G → α) : Prop :=
  (∀ k ∈ OrientedRigidity.genomeNodes (L := L) hG S,
    ∃! w, w ∈ OrientedRigidity.support (L := L) hG S ∧
      OrientedRigidity.winPrefix w = k) ∧
  (∀ k ∈ OrientedRigidity.genomeNodes (L := L) hG S,
    ∃! w, w ∈ OrientedRigidity.support (L := L) hG S ∧
      OrientedRigidity.winSuffix w = k)

/-- Agreement from fixed starts, used for both extension phases:
`f ≤ G` and triple agreement on `base + f`. -/
private def AgreeFrom {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (a b c base : ℕ) (f : ℕ) : Prop :=
  f ≤ G ∧ TripleAgree hG S a b c (base + f)

/-! ## Basic `cyc` congruences -/

/-- `cyc` depends only on the residue mod `G`. -/
private theorem cyc_congr {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    {x y : ℕ} (h : x % G = y % G) :
    OrientedRigidity.cyc hG S x = OrientedRigidity.cyc hG S y := by
  unfold OrientedRigidity.cyc
  exact congrArg S (Fin.ext h)

/-- Shifting a position by a full turn changes nothing. -/
private theorem cyc_add_G {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (x : ℕ) :
    OrientedRigidity.cyc hG S (x + G) = OrientedRigidity.cyc hG S x := by
  apply cyc_congr hG S
  rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]

/-- `(x + G) % G = x % G`, the residue form. -/
private theorem add_G_mod {G : ℕ} (x : ℕ) :
    (x + G) % G = x % G := by
  rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]

/-- A period iterates: agreement survives shifts by multiples of `p`. -/
private theorem per_add_mul {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (p : ℕ) (hper : IsPeriod hG S p) (i q : ℕ) :
    OrientedRigidity.cyc hG S i =
      OrientedRigidity.cyc hG S (i + p * q) := by
  induction q with
  | zero => simp
  | succ n ih =>
      have h1 := hper (i + p * n)
      rw [Nat.mul_succ]
      have heq : i + (p * n + p) = (i + p * n) + p := by omega
      rw [heq]
      exact ih.trans h1

/-- Under period `p`, a window starting at `x` agrees with the window
starting at the residue `x % p`. -/
private theorem cyc_residue_add {α : Type} {G : ℕ} (hG : 0 < G)
    (S : Fin G → α) (p : ℕ) (hper : IsPeriod hG S p) (x d : ℕ) :
    OrientedRigidity.cyc hG S (x + d) =
      OrientedRigidity.cyc hG S (x % p + d) := by
  have hdecomp : x + d = (x % p + d) + p * (x / p) := by
    have h := Nat.mod_add_div x p
    omega
  rw [hdecomp]
  exact (per_add_mul hG S p hper _ _).symm

/-- `cyc` respects congruence mod `p` under a period `p`. -/
private theorem cyc_per_congr {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (p : ℕ) (hper : IsPeriod hG S p) {x y : ℕ} (h : x % p = y % p) :
    OrientedRigidity.cyc hG S x = OrientedRigidity.cyc hG S y := by
  have e1 := cyc_residue_add hG S p hper x 0
  have e2 := cyc_residue_add hG S p hper y 0
  simp only [Nat.add_zero] at e1 e2
  rw [e1, e2, h]

/-! ## Long agreement between distinct residues breaks primitivity -/

/-- Agreement on `≥ G` consecutive positions between starts in distinct
residue classes forces shift-invariance (hence non-primitivity). The
shift is `s = (b % G + G - a % G) % G`; the witness offset
`d = (i + G - a % G) % G` places `a + d` over `i` and `b + d` over
`i + s`, all inside the agreement range since `d < G ≤ ℓ`. -/
theorem not_primitive_of_ge_G_agree {α : Type} {G : ℕ} (hG : 0 < G)
    (S : Fin G → α) (a b ℓ : ℕ) (hab : a % G ≠ b % G) (hℓ : G ≤ ℓ)
    (h : ∀ d : ℕ, d < ℓ →
      OrientedRigidity.cyc hG S (a + d) =
        OrientedRigidity.cyc hG S (b + d)) :
    ¬ IsPrimitive hG S := by
  intro hprim
  set A : ℕ := a % G with hA
  set B : ℕ := b % G with hB
  have hAG : A < G := Nat.mod_lt _ hG
  have hBG : B < G := Nat.mod_lt _ hG
  have hAB : A ≠ B := hab
  set s : ℕ := (B + G - A) % G with hs
  have hsLt : s < G := Nat.mod_lt _ hG
  have hsPos : 0 < s := by
    rw [hs]
    by_cases hle : A ≤ B
    · have heq : B + G - A = G + (B - A) := by omega
      rw [heq, show (G + (B - A)) % G = (B - A) % G from by
        rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]]
      rw [Nat.mod_eq_of_lt (by omega : B - A < G)]
      omega
    · have heq : B + G - A = G - (A - B) := by omega
      rw [heq, Nat.mod_eq_of_lt (by omega : G - (A - B) < G)]
      omega
  apply hprim s hsPos hsLt
  intro i
  set d : ℕ := (i + G - A) % G with hd
  have hdLt : d < G := Nat.mod_lt _ hG
  have hag := h d (lt_of_lt_of_le hdLt hℓ)
  have hmodd : d % G = (i + G - A) % G := by rw [hd, Nat.mod_mod]
  have key1 : (a + d) % G = i % G := by
    have e : (a + d) % G = (A + (i + G - A)) % G := by
      have g1 : (a + d) % G = ((a % G) + (d % G)) % G := Nat.add_mod _ _ _
      have g2 : (A + (i + G - A)) % G = ((A % G) + ((i + G - A) % G)) % G :=
        Nat.add_mod _ _ _
      have haA : a % G = A := hA.symm
      have hAA : A % G = A := Nat.mod_eq_of_lt hAG
      rw [g1, g2, haA, hmodd, hAA]
    have f : (A + (i + G - A)) % G = i % G := by
      have heq : A + (i + G - A) = i + G := by
        have hleA : A ≤ i + G := by omega
        omega
      rw [heq, add_G_mod]
    exact e.trans f
  have key2 : (b + d) % G = (i + s) % G := by
    have e1 : (b + d) % G = (B + (i + G - A)) % G := by
      have g1 : (b + d) % G = ((b % G) + (d % G)) % G := Nat.add_mod _ _ _
      have g2 : (B + (i + G - A)) % G = ((B % G) + ((i + G - A) % G)) % G :=
        Nat.add_mod _ _ _
      have hbB : b % G = B := hB.symm
      have hBB : B % G = B := Nat.mod_eq_of_lt hBG
      rw [g1, g2, hbB, hmodd, hBB]
    have e2 : (i + s) % G = (B + (i + G - A)) % G := by
      have hsmod : s % G = (B + G - A) % G := by rw [hs, Nat.mod_mod]
      have g1 : (i + s) % G = ((i % G) + (s % G)) % G := Nat.add_mod _ _ _
      have g2 : (i + (B + G - A)) % G = ((i % G) + ((B + G - A) % G)) % G :=
        Nat.add_mod _ _ _
      have congr1 : (i + s) % G = (i + (B + G - A)) % G := by
        rw [g1, g2, hsmod]
      have heq : i + (B + G - A) = B + (i + G - A) := by
        have h1 : A ≤ B + G := by omega
        have h2 : A ≤ i + G := by omega
        omega
      rw [congr1, heq]
    exact e1.trans e2.symm
  calc OrientedRigidity.cyc hG S i
      = OrientedRigidity.cyc hG S (a + d) := cyc_congr hG S key1.symm
    _ = OrientedRigidity.cyc hG S (b + d) := hag
    _ = OrientedRigidity.cyc hG S (i + s) := cyc_congr hG S key2

/-! ## Shared extension engine: small periods and two-sided extension -/

/-- Pair agreement on `≥ p` consecutive positions between starts in
distinct residues mod `p` forces a strictly smaller period (the periodic
analogue of `not_primitive_of_ge_G_agree`, used for Lemma C). The shift
is `s = (b % p + p - a % p) % p`; offsets are placed by residues mod `p`
and transported back with `cyc_per_congr`. -/
theorem small_period_of_ge_p_agree {α : Type} {G : ℕ} (hG : 0 < G)
    (S : Fin G → α) (p : ℕ) (hp0 : 0 < p) (hper : IsPeriod hG S p)
    (a b ℓ : ℕ) (hab : a % p ≠ b % p) (hℓ : p ≤ ℓ)
    (h : ∀ d : ℕ, d < ℓ →
      OrientedRigidity.cyc hG S (a + d) =
        OrientedRigidity.cyc hG S (b + d)) :
    ∃ s : ℕ, 0 < s ∧ s < p ∧ IsPeriod hG S s := by
  set A : ℕ := a % p with hA
  set B : ℕ := b % p with hB
  have hAG : A < p := Nat.mod_lt _ hp0
  have hBG : B < p := Nat.mod_lt _ hp0
  have hAB : A ≠ B := hab
  set s : ℕ := (B + p - A) % p with hs
  have hsLt : s < p := Nat.mod_lt _ hp0
  have hsPos : 0 < s := by
    rw [hs]
    by_cases hle : A ≤ B
    · have heq : B + p - A = p + (B - A) := by omega
      rw [heq, show (p + (B - A)) % p = (B - A) % p from by
        rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]]
      rw [Nat.mod_eq_of_lt (by omega : B - A < p)]
      omega
    · have heq : B + p - A = p - (A - B) := by omega
      rw [heq, Nat.mod_eq_of_lt (by omega : p - (A - B) < p)]
      omega
  refine ⟨s, hsPos, hsLt, ?_⟩
  intro i
  set d : ℕ := (i + p - A) % p with hd
  have hdLt : d < p := Nat.mod_lt _ hp0
  have hag := h d (lt_of_lt_of_le hdLt hℓ)
  have hmodd : d % p = (i + p - A) % p := by rw [hd, Nat.mod_mod]
  have key1 : (a + d) % p = i % p := by
    have e : (a + d) % p = (A + (i + p - A)) % p := by
      have g1 : (a + d) % p = ((a % p) + (d % p)) % p := Nat.add_mod _ _ _
      have g2 : (A + (i + p - A)) % p = ((A % p) + ((i + p - A) % p)) % p :=
        Nat.add_mod _ _ _
      have haA : a % p = A := hA.symm
      have hAA : A % p = A := Nat.mod_eq_of_lt hAG
      rw [g1, g2, haA, hmodd, hAA]
    have f : (A + (i + p - A)) % p = i % p := by
      have heq : A + (i + p - A) = i + p := by
        have hleA : A ≤ i + p := by omega
        omega
      rw [heq, add_G_mod]
    exact e.trans f
  have key2 : (b + d) % p = (i + s) % p := by
    have e1 : (b + d) % p = (B + (i + p - A)) % p := by
      have g1 : (b + d) % p = ((b % p) + (d % p)) % p := Nat.add_mod _ _ _
      have g2 : (B + (i + p - A)) % p = ((B % p) + ((i + p - A) % p)) % p :=
        Nat.add_mod _ _ _
      have hbB : b % p = B := hB.symm
      have hBB : B % p = B := Nat.mod_eq_of_lt hBG
      rw [g1, g2, hbB, hmodd, hBB]
    have e2 : (i + s) % p = (B + (i + p - A)) % p := by
      have hsmod : s % p = (B + p - A) % p := by rw [hs, Nat.mod_mod]
      have g1 : (i + s) % p = ((i % p) + (s % p)) % p := Nat.add_mod _ _ _
      have g2 : (i + (B + p - A)) % p = ((i % p) + ((B + p - A) % p)) % p :=
        Nat.add_mod _ _ _
      have congr1 : (i + s) % p = (i + (B + p - A)) % p := by
        rw [g1, g2, hsmod]
      have heq : i + (B + p - A) = B + (i + p - A) := by
        have h1 : A ≤ B + p := by omega
        have h2 : A ≤ i + p := by omega
        omega
      rw [congr1, heq]
    exact e1.trans e2.symm
  calc OrientedRigidity.cyc hG S i
      = OrientedRigidity.cyc hG S (a + d) :=
        cyc_per_congr hG S p hper key1.symm
    _ = OrientedRigidity.cyc hG S (b + d) := hag
    _ = OrientedRigidity.cyc hG S (i + s) :=
        cyc_per_congr hG S p hper key2

/-- **Shared two-sided maximal-extension engine (Lemmas B and C).**
Three starts in pairwise distinct residues mod `G` agreeing on `L - 1`
positions are extended maximally backwards (bounded maximum over
`Icc 0 G`) and then forwards. Either some phase reaches total length
`≥ G` — discharged by the caller-supplied `hbig` escape, which
additionally receives the back-shift `b` witnessing the shifted form of
the escape pair — or both flanks differ, yielding a long maximal triple
that contradicts `hno`. Lemma B escapes via non-primitivity; Lemma C
via a strictly smaller period. -/
private theorem extend_triple {α : Type} {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) (hL : 2 ≤ L) (a₁ a₂ a₃ : ℕ)
    (hdist : a₁ % G ≠ a₂ % G ∧ a₂ % G ≠ a₃ % G ∧ a₁ % G ≠ a₃ % G)
    (hag : TripleAgree hG S a₁ a₂ a₃ (L - 1))
    (hno : ¬ HasLongTripleRepeat hG S L)
    (hbig : ∀ b₁ b₂ ℓ : ℕ, b₁ % G ≠ b₂ % G → G ≤ ℓ →
      (∀ d : ℕ, d < ℓ → OrientedRigidity.cyc hG S (b₁ + d) =
        OrientedRigidity.cyc hG S (b₂ + d)) →
      ∀ b : ℕ, b ≤ G → b₁ = a₁ + G - b → b₂ = a₂ + G - b → False) :
    False := by
  classical
  -- Length regime for the extension bounds below (`L ≥ 2`, hence the
  -- initial window `L - 1` is nonempty); named explicitly for the record.
  have _hLuse : 2 ≤ L := hL
  -- Backward phase: maximal uniform back-shift.
  have hback0 : AgreeFrom hG S (a₁ + G - 0) (a₂ + G - 0)
      (a₃ + G - 0) (L - 1) 0 := by
    refine ⟨Nat.zero_le _, ?_⟩
    intro d hd
    have r1e : a₁ + G - 0 + d = (a₁ + d) + G := by omega
    have r2e : a₂ + G - 0 + d = (a₂ + d) + G := by omega
    have r3e : a₃ + G - 0 + d = (a₃ + d) + G := by omega
    simp only [r1e, r2e, r3e, cyc_add_G hG S]
    have hd' : d < L - 1 := by omega
    exact hag d hd'
  set backSet : Finset ℕ :=
    (Finset.Icc 0 G).filter
      (fun b => AgreeFrom hG S (a₁ + G - b) (a₂ + G - b)
        (a₃ + G - b) (L - 1) b) with hbackSet
  have hbackNe : backSet.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [hbackSet, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.zero_le _, Nat.zero_le _⟩, hback0⟩
  set bstar : ℕ := backSet.max' hbackNe with hbstar
  have hbstar_mem : bstar ∈ backSet := Finset.max'_mem _ _
  have hbstar_le : ∀ b ∈ backSet, b ≤ bstar :=
    fun b hb => Finset.le_max' _ _ hb
  have hbstar_P := (Finset.mem_filter.mp hbstar_mem).2
  obtain ⟨hbstar_leG, hbstar_ag⟩ := hbstar_P
  -- Uniform back-shifts preserve residue distinctness.
  have shiftNe : ∀ u v : ℕ, u % G ≠ v % G →
      (u + G - bstar) % G ≠ (v + G - bstar) % G := by
    intro u v huv hcon
    apply huv
    have hC : u + G - bstar = u + (G - bstar) := by omega
    have hC2 : v + G - bstar = v + (G - bstar) := by omega
    rw [hC, hC2] at hcon
    have hme : u ≡ v [MOD G] :=
      Nat.ModEq.add_right_cancel' (G - bstar) hcon
    exact hme
  have hq12 : (a₁ + G - bstar) % G ≠ (a₂ + G - bstar) % G :=
    shiftNe _ _ hdist.1
  have hq23 : (a₂ + G - bstar) % G ≠ (a₃ + G - bstar) % G :=
    shiftNe _ _ hdist.2.1
  have hq13 : (a₁ + G - bstar) % G ≠ (a₃ + G - bstar) % G :=
    shiftNe _ _ hdist.2.2
  by_cases hblt : L - 1 + bstar < G
  · -- The total stays below `G`: exhibit a long maximal triple.
    have hbsG : bstar + 1 ≤ G := by omega
    -- Preceding flanks differ, else `bstar` was not maximal.
    have hpre : ¬ (OrientedRigidity.cyc hG S ((a₁ + G - bstar) + G - 1) =
            OrientedRigidity.cyc hG S ((a₂ + G - bstar) + G - 1) ∧
          OrientedRigidity.cyc hG S ((a₂ + G - bstar) + G - 1) =
            OrientedRigidity.cyc hG S ((a₃ + G - bstar) + G - 1)) := by
      intro hcon
      have hstep : AgreeFrom hG S (a₁ + G - (bstar + 1))
          (a₂ + G - (bstar + 1)) (a₃ + G - (bstar + 1))
          (L - 1) (bstar + 1) := by
        refine ⟨hbsG, ?_⟩
        intro d hd
        have p1 : a₁ + G - (bstar + 1) + d =
            ((a₁ + G - bstar) - 1) + d := by omega
        have p2 : a₂ + G - (bstar + 1) + d =
            ((a₂ + G - bstar) - 1) + d := by omega
        have p3 : a₃ + G - (bstar + 1) + d =
            ((a₃ + G - bstar) - 1) + d := by omega
        rw [p1, p2, p3]
        by_cases hd0 : d = 0
        · subst hd0
          rw [Nat.add_zero, Nat.add_zero, Nat.add_zero]
          have q1 : 1 ≤ a₁ + G - bstar := by omega
          have q2 : 1 ≤ a₂ + G - bstar := by omega
          have q3 : 1 ≤ a₃ + G - bstar := by omega
          have b1 : ((a₁ + G - bstar) - 1) % G =
              ((a₁ + G - bstar) + G - 1) % G := by
            have ee : (a₁ + G - bstar) + G - 1 =
                ((a₁ + G - bstar) - 1) + G := by omega
            rw [ee, add_G_mod]
          have b2 : ((a₂ + G - bstar) - 1) % G =
              ((a₂ + G - bstar) + G - 1) % G := by
            have ee : (a₂ + G - bstar) + G - 1 =
                ((a₂ + G - bstar) - 1) + G := by omega
            rw [ee, add_G_mod]
          have b3 : ((a₃ + G - bstar) - 1) % G =
              ((a₃ + G - bstar) + G - 1) % G := by
            have ee : (a₃ + G - bstar) + G - 1 =
                ((a₃ + G - bstar) - 1) + G := by omega
            rw [ee, add_G_mod]
          have c1 := cyc_congr hG S b1
          have c2 := cyc_congr hG S b2
          have c3 := cyc_congr hG S b3
          exact ⟨c1.trans (hcon.1.trans c2.symm), c2.trans (hcon.2.trans c3.symm)⟩
        · obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
          have q1 : 1 ≤ a₁ + G - bstar := by omega
          have q2 : 1 ≤ a₂ + G - bstar := by omega
          have q3 : 1 ≤ a₃ + G - bstar := by omega
          have s1 : (a₁ + G - bstar) - 1 + (e + 1) =
              (a₁ + G - bstar) + e := by omega
          have s2 : (a₂ + G - bstar) - 1 + (e + 1) =
              (a₂ + G - bstar) + e := by omega
          have s3 : (a₃ + G - bstar) - 1 + (e + 1) =
              (a₃ + G - bstar) + e := by omega
          rw [s1, s2, s3]
          have he : e < L - 1 + bstar := by omega
          exact hbstar_ag e he
      have hmem : bstar + 1 ∈ backSet := by
        simp only [hbackSet, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨Nat.zero_le _, hbsG⟩, hstep⟩
      have hle := hbstar_le (bstar + 1) hmem
      omega
    -- Forward phase from the back-shifted starts.
    set fwdSet : Finset ℕ :=
      (Finset.Icc 0 G).filter
        (fun f => AgreeFrom hG S (a₁ + G - bstar) (a₂ + G - bstar)
          (a₃ + G - bstar) (L - 1 + bstar) f) with hfwdSet
    have hfwdNe : fwdSet.Nonempty := by
      refine ⟨0, ?_⟩
      simp only [hfwdSet, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.zero_le _, Nat.zero_le _⟩, Nat.zero_le _, ?_⟩
      intro d hd
      have hd' : d < L - 1 + bstar := by omega
      exact hbstar_ag d hd'
    set fstar : ℕ := fwdSet.max' hfwdNe with hfstar
    have hfstar_mem : fstar ∈ fwdSet := Finset.max'_mem _ _
    have hfstar_le : ∀ f ∈ fwdSet, f ≤ fstar :=
      fun f hf => Finset.le_max' _ _ hf
    have hfstar_P := (Finset.mem_filter.mp hfstar_mem).2
    obtain ⟨hfstar_leG, hfstar_ag⟩ := hfstar_P
    by_cases hflt : L - 1 + bstar + fstar < G
    · -- Following flanks differ, else `fstar` was not maximal.
      have hfol : ¬ (OrientedRigidity.cyc hG S
              ((a₁ + G - bstar) + (L - 1 + bstar + fstar)) =
              OrientedRigidity.cyc hG S
                ((a₂ + G - bstar) + (L - 1 + bstar + fstar)) ∧
            OrientedRigidity.cyc hG S
              ((a₂ + G - bstar) + (L - 1 + bstar + fstar)) =
              OrientedRigidity.cyc hG S
                ((a₃ + G - bstar) + (L - 1 + bstar + fstar))) := by
        intro hcon
        have hstep : AgreeFrom hG S (a₁ + G - bstar)
            (a₂ + G - bstar) (a₃ + G - bstar)
            (L - 1 + bstar) (fstar + 1) := by
          refine ⟨by omega, ?_⟩
          have eqlen : L - 1 + bstar + (fstar + 1) =
              (L - 1 + bstar + fstar) + 1 := by omega
          rw [eqlen]
          intro d hd
          by_cases hdl : d < L - 1 + bstar + fstar
          · exact hfstar_ag d hdl
          · have hdeq : d = L - 1 + bstar + fstar := by omega
            subst hdeq
            exact hcon
        have hmem : fstar + 1 ∈ fwdSet := by
          simp only [hfwdSet, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨Nat.zero_le _, by omega⟩, hstep⟩
        have hle := hfstar_le (fstar + 1) hmem
        omega
      -- The long maximal triple.
      apply hno
      exact ⟨a₁ + G - bstar, a₂ + G - bstar, a₃ + G - bstar,
        L - 1 + bstar + fstar, by omega, hflt, hq12, hq23, hq13,
        hfstar_ag, hpre, hfol⟩
    · -- Forward total reaches `G`: caller's escape.
      have hflt' : G ≤ L - 1 + bstar + fstar := not_lt.mp hflt
      exact hbig _ _ _ hq12 hflt' (fun d hd => (hfstar_ag d hd).1)
        bstar hbstar_leG rfl rfl
  · -- Backward total reaches `G`: caller's escape.
    have hblt' : G ≤ L - 1 + bstar := not_lt.mp hblt
    exact hbig _ _ _ hq12 hblt' (fun d hd => (hbstar_ag d hd).1)
      bstar hbstar_leG rfl rfl

/-! ## Primitive branch: the `(L-1)`-window cap (note Lemma B) -/

/-- Three distinct elements from `3 ≤ card`. -/
private theorem three_of_card_ge_three {β : Type} [DecidableEq β] {s : Finset β}
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

/-- **Lemma B (primitive extension), word-level cap.** A primitive
circular word with no long Bresler triple repeat has every
`(L-1)`-window multiplicity at most `2`. Proof: three starts sharing an
`(L-1)`-window are extended maximally backwards (bounded maximum over
`Icc 0 G`) and then forwards; either the total reaches `G` (contradicting
primitivity via `not_primitive_of_ge_G_agree`) or both flanks differ,
exhibiting a long maximal triple. -/
theorem primitive_nodeCount_le_two {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) (S : Fin G → α) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hprim : IsPrimitive hG S)
    (hno : ¬ HasLongTripleRepeat hG S L) :
    ∀ k : Fin (L - 1) → α, k ∈ OrientedRigidity.genomeNodes hG S →
      OrientedRigidity.nodeCount hG S k ≤ 2 := by
  classical
  intro k hk
  by_contra hgt
  -- Regime hypothesis, kept explicit for the record (`L ≤ G` orients the
  -- `(L-1)`-windows against the circular word; the proof needs `2 ≤ L`).
  have _hLGuse : L ≤ G := hLG
  have h3 : 3 ≤ (Finset.univ.filter
      (fun r : Fin G => OrientedRigidity.nodeWindow hG S r = k)).card := by
    have hlt : 2 < (Finset.univ.filter
        (fun r : Fin G => OrientedRigidity.nodeWindow hG S r = k)).card :=
      lt_of_not_ge hgt
    omega
  obtain ⟨r1, r2, r3, hr1, hr2, hr3, h12, h13, h23⟩ :=
    three_of_card_ge_three h3
  have e1 : OrientedRigidity.nodeWindow hG S r1 = k :=
    (Finset.mem_filter.mp hr1).2
  have e2 : OrientedRigidity.nodeWindow hG S r2 = k :=
    (Finset.mem_filter.mp hr2).2
  have e3 : OrientedRigidity.nodeWindow hG S r3 = k :=
    (Finset.mem_filter.mp hr3).2
  have hAG : TripleAgree hG S r1.val r2.val r3.val (L - 1) := by
    intro d hd
    have f12 := congrFun (e1.trans e2.symm) ⟨d, hd⟩
    have f23 := congrFun (e2.trans e3.symm) ⟨d, hd⟩
    exact ⟨f12, f23⟩
  have m1 : r1.val % G = r1.val := Nat.mod_eq_of_lt r1.isLt
  have m2 : r2.val % G = r2.val := Nat.mod_eq_of_lt r2.isLt
  have m3 : r3.val % G = r3.val := Nat.mod_eq_of_lt r3.isLt
  have hdist : r1.val % G ≠ r2.val % G ∧ r2.val % G ≠ r3.val % G ∧
      r1.val % G ≠ r3.val % G := by
    rw [m1, m2, m3]
    exact ⟨fun h => h12 (Fin.ext h), fun h => h23 (Fin.ext h),
      fun h => h13 (Fin.ext h)⟩
  exact extend_triple hG S hL r1.val r2.val r3.val hdist hAG hno
    (fun b₁ b₂ ℓ hne hle hag _ _ _ _ =>
      (not_primitive_of_ge_G_agree hG S b₁ b₂ ℓ hne hle hag) hprim)

/-- **Primitive route end-to-end.** Under primitivity and no long triple
repeat, every same-length spelled candidate has exactly the truth's
spectrum (via `rigidity_same_spectrum` and the cap above). -/
theorem primitive_rigidity_same_spectrum {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) (S : Fin G → α) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hprim : IsPrimitive hG S)
    (hno : ¬ HasLongTripleRepeat hG S L)
    (B : (Fin L → α) → ℕ)
    (hBsup : ∀ w, w ∈ OrientedRigidity.support hG S ↔ 0 < B w)
    (hBbal : OrientedRigidity.Balanced OrientedRigidity.winPrefix
      OrientedRigidity.winSuffix (OrientedRigidity.genomeNodes hG S)
      (OrientedRigidity.support hG S) B)
    (hBtot : ∑ w ∈ OrientedRigidity.support hG S, B w = G) :
    ∀ w, B w = OrientedRigidity.specCount hG S w := by
  apply OrientedRigidity.rigidity_same_spectrum hG S B hBsup hBbal hBtot
  intro k hk
  exact primitive_nodeCount_le_two hG S hL hLG hprim hno k hk

/-! ## Periodic branch: abstract cycle rigidity -/

/-- **Abstract simple-cycle rigidity.** On a strongly connected support
where every node has exactly one outgoing and exactly one incoming edge,
any two positive balanced circulations with equal totals agree. Strong
connectivity is needed: on a disjoint union of cycles, distinct per-component
constants give distinct circulations with the same total. -/
theorem unique_circulation_of_cycle {V E : Type} [DecidableEq V]
    [DecidableEq E] (tail head : E → V) (nodes : Finset V)
    (edges : Finset E) (A B : E → ℕ)
    (hmem : ∀ e ∈ edges, tail e ∈ nodes ∧ head e ∈ nodes)
    (hApos : ∀ e ∈ edges, 1 ≤ A e)
    (hBpos : ∀ e ∈ edges, 1 ≤ B e)
    (hAbal : ∀ v ∈ nodes,
      ∑ e ∈ edges.filter (fun e => tail e = v), A e =
      ∑ e ∈ edges.filter (fun e => head e = v), A e)
    (hBbal : ∀ v ∈ nodes,
      ∑ e ∈ edges.filter (fun e => tail e = v), B e =
      ∑ e ∈ edges.filter (fun e => head e = v), B e)
    (htot : ∑ e ∈ edges, A e = ∑ e ∈ edges, B e)
    (huniqOut : ∀ v ∈ nodes, ∃! e, e ∈ edges ∧ tail e = v)
    (huniqIn : ∀ v ∈ nodes, ∃! e, e ∈ edges ∧ head e = v)
    (hstrong : OrientedRigidity.StronglyConnected tail head nodes edges)
    (hne : edges.Nonempty) :
    ∀ e ∈ edges, A e = B e := by
  -- Each circulation is constant on the support.
  have const : ∀ F : E → ℕ, (∀ e ∈ edges, 1 ≤ F e) →
      (∀ v ∈ nodes, ∑ e ∈ edges.filter (fun e => tail e = v), F e =
        ∑ e ∈ edges.filter (fun e => head e = v), F e) →
      ∀ e₁ e₂ : E, e₁ ∈ edges → e₂ ∈ edges → F e₁ = F e₂ := by
    intro F hFpos hFbal e₁ e₂ he₁ he₂
    have hexOut : ∀ v : V, ∃ e, e ∈ edges ∧ (v ∈ nodes → tail e = v) := by
      intro v
      by_cases hv : v ∈ nodes
      · obtain ⟨e, he, hte⟩ := (huniqOut v hv).exists
        exact ⟨e, he, fun _ => hte⟩
      · obtain ⟨e, he⟩ := hne
        exact ⟨e, he, fun h => absurd h hv⟩
    choose outE houtE using hexOut
    have hexIn : ∀ v : V, ∃ e, e ∈ edges ∧ (v ∈ nodes → head e = v) := by
      intro v
      by_cases hv : v ∈ nodes
      · obtain ⟨e, he, hhe⟩ := (huniqIn v hv).exists
        exact ⟨e, he, fun _ => hhe⟩
      · obtain ⟨e, he⟩ := hne
        exact ⟨e, he, fun h => absurd h hv⟩
    choose inE hinE using hexIn
    -- Balance at a node equates its unique out- and in-edge values.
    have hnode : ∀ k : V, k ∈ nodes → F (outE k) = F (inE k) := by
      intro k hk
      have hoE := houtE k
      have hiE := hinE k
      have hbal := hFbal k hk
      have hout_mem : outE k ∈ edges.filter (fun e => tail e = k) :=
        Finset.mem_filter.mpr ⟨hoE.1, hoE.2 hk⟩
      have hin_mem : inE k ∈ edges.filter (fun e => head e = k) :=
        Finset.mem_filter.mpr ⟨hiE.1, hiE.2 hk⟩
      have hout_uniq : ∀ x ∈ edges.filter (fun e => tail e = k), x = outE k := by
        intro x hx
        exact (huniqOut k hk).unique (Finset.mem_filter.mp hx)
          ⟨hoE.1, hoE.2 hk⟩
      have hin_uniq : ∀ x ∈ edges.filter (fun e => head e = k), x = inE k := by
        intro x hx
        exact (huniqIn k hk).unique (Finset.mem_filter.mp hx)
          ⟨hiE.1, hiE.2 hk⟩
      have hoS : edges.filter (fun e => tail e = k) = {outE k} :=
        Finset.eq_singleton_iff_unique_mem.mpr ⟨hout_mem, hout_uniq⟩
      have hiS : edges.filter (fun e => head e = k) = {inE k} :=
        Finset.eq_singleton_iff_unique_mem.mpr ⟨hin_mem, hin_uniq⟩
      rw [hoS, hiS, Finset.sum_singleton, Finset.sum_singleton] at hbal
      exact hbal
    -- The value propagates along directed paths.
    have key : ∀ (v : V)
        (h : OrientedRigidity.Reachable tail head edges (head e₁) v),
        v ∈ nodes → F e₁ = F (outE v) := by
      intro v h
      induction h with
      | refl =>
          intro hv
          have h1 := hnode (head e₁) ((hmem e₁ he₁).2)
          have heq : inE (head e₁) = e₁ :=
            (huniqIn (head e₁) ((hmem e₁ he₁).2)).unique
              ⟨(hinE (head e₁)).1, (hinE (head e₁)).2 ((hmem e₁ he₁).2)⟩
              ⟨he₁, rfl⟩
          rw [heq] at h1
          exact h1.symm
      | step f hpred hff htf hhf ih =>
          intro hv
          have hmemf : tail f ∈ nodes := (hmem f hff).1
          rw [htf] at hmemf
          have ih' := ih hmemf
          have hfo : outE _ = f :=
            (huniqOut _ hmemf).unique
              ⟨(houtE _).1, (houtE _).2 hmemf⟩ ⟨hff, htf⟩
          have hfi : inE _ = f :=
            (huniqIn _ hv).unique
              ⟨(hinE _).1, (hinE _).2 hv⟩ ⟨hff, hhf⟩
          have hnv := hnode _ hv
          rw [hfi] at hnv
          rw [hfo] at ih'
          exact ih'.trans hnv.symm
    have hpath := hstrong (head e₁) ((hmem e₁ he₁).2)
      (tail e₂) ((hmem e₂ he₂).1)
    have hte : tail e₂ ∈ nodes := (hmem e₂ he₂).1
    have h1 := key (tail e₂) hpath hte
    have h2 : outE (tail e₂) = e₂ :=
      (huniqOut (tail e₂) hte).unique
        ⟨(houtE (tail e₂)).1, (houtE (tail e₂)).2 hte⟩ ⟨he₂, rfl⟩
    rw [h2] at h1
    exact h1
  have hAc := const A hApos hAbal
  have hBc := const B hBpos hBbal
  obtain ⟨e₀, he₀⟩ := hne
  have hcard : (0 : ℕ) < edges.card := Finset.card_pos.mpr ⟨e₀, he₀⟩
  have hAeq : ∑ e ∈ edges, A e = edges.card * A e₀ := by
    have h : ∑ e ∈ edges, A e = ∑ _e ∈ edges, A e₀ :=
      Finset.sum_congr rfl (fun e he => hAc e e₀ he he₀)
    rw [h, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  have hBeq : ∑ e ∈ edges, B e = edges.card * B e₀ := by
    have h : ∑ e ∈ edges, B e = ∑ _e ∈ edges, B e₀ :=
      Finset.sum_congr rfl (fun e he => hBc e e₀ he he₀)
    rw [h, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  have hval : A e₀ = B e₀ := by
    have hAB : edges.card * A e₀ = edges.card * B e₀ := by
      rw [← hAeq, ← hBeq, htot]
    exact mul_left_cancel₀ (by omega : edges.card ≠ 0) hAB
  intro e he
  exact (hAc e e₀ he he₀).trans (hval.trans (hBc e e₀ he he₀).symm)

/-! ## Periodic branch: word-level cycle shape -/

/-- The window support is nonempty for `0 < G`. -/
theorem support_nonempty {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) : (OrientedRigidity.support (L := L) hG S).Nonempty :=
  ⟨_, Finset.mem_image.mpr ⟨⟨0, hG⟩, Finset.mem_univ _, rfl⟩⟩

/-- The prefix of a window is the node window at the same start. -/
private theorem pre_window {α : Type} {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (r : Fin G) :
    OrientedRigidity.winPrefix (OrientedRigidity.window (L := L) hG S r) =
      OrientedRigidity.nodeWindow (L := L) hG S r := rfl

/-- The suffix of a window, spelled out explicitly (avoids the private
`nextStart`). -/
private theorem suf_window {α : Type} {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (r : Fin G) :
    OrientedRigidity.winSuffix (OrientedRigidity.window (L := L) hG S r) =
      (fun d : Fin (L - 1) =>
        OrientedRigidity.cyc hG S (r.val + (d.val + 1))) := rfl

/-- Every length-`L` window equals the window at its residue mod `p`. -/
private theorem window_residue {α : Type} {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) (p : ℕ) (hp0 : 0 < p) (hple : p ≤ G)
    (hper : IsPeriod hG S p) (t : Fin G) :
    ∃ r : Fin G, r.val < p ∧ OrientedRigidity.window (L := L) hG S t =
      OrientedRigidity.window (L := L) hG S r := by
  refine ⟨⟨t.val % p, lt_of_lt_of_le (Nat.mod_lt _ hp0) hple⟩,
    Nat.mod_lt _ hp0, ?_⟩
  funext d
  exact cyc_residue_add hG S p hper t.val d.val

/-- Every length-`(L-1)` node window equals the one at its residue mod `p`. -/
private theorem nodeWindow_residue {α : Type} {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) (p : ℕ) (hp0 : 0 < p) (hple : p ≤ G)
    (hper : IsPeriod hG S p) (t : Fin G) :
    ∃ r : Fin G, r.val < p ∧ OrientedRigidity.nodeWindow (L := L) hG S t =
      OrientedRigidity.nodeWindow (L := L) hG S r := by
  refine ⟨⟨t.val % p, lt_of_lt_of_le (Nat.mod_lt _ hp0) hple⟩,
    Nat.mod_lt _ hp0, ?_⟩
  funext d
  exact cyc_residue_add hG S p hper t.val d.val

/-- One step back within residues mod `p` returns to the residue:
`(((t + p - 1) % p) + 1) % p = t % p`. -/
private theorem back_step_residue (t p : ℕ) (hp0 : 0 < p) :
    (((t % p + p - 1) % p) + 1) % p = t % p := by
  have h1 : ((t % p + p - 1) % p + 1) % p = ((t % p + p - 1) + 1) % p := by
    rw [Nat.mod_add_mod]
  rw [h1]
  have h2 : t % p + p - 1 + 1 = t % p + p := by
    have : t % p + p ≥ 1 := by omega
    omega
  rw [h2, add_G_mod, Nat.mod_mod]
/-- **Lemma C (periodic extension), word-level distinctness.** Under a
minimal period `p`, if two residues below `p` carried the same
length-`(L-1)` window, the three starts `i`, `j`, `i + p` (pairwise
distinct mod `G`, using `i + p < G` from `p ∣ G` and `p < G`) would feed
the shared extension engine: either some phase reaches total length
`≥ G`, and the shifted pair — still distinct mod `p` by uniform-shift
injectivity — yields a strictly smaller period via
`small_period_of_ge_p_agree`, contradicting minimality; or both flanks
differ, exhibiting a long maximal triple. Requires `2 ≤ L` so the
initial window is nonempty. -/
theorem periodic_factor_distinct {α : Type} {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) (p : ℕ) (hL : 2 ≤ L)
    (hmin : HasMinimalPeriod hG S p)
    (hno : ¬ HasLongTripleRepeat hG S L) :
    ∀ i j : ℕ, i < p → j < p →
      (∀ d : ℕ, d < L - 1 →
        OrientedRigidity.cyc hG S (i + d) =
          OrientedRigidity.cyc hG S (j + d)) → i = j := by
  obtain ⟨hp0, hpG, hGp, hper, hsmall⟩ := hmin
  have hple : p ≤ G := le_of_lt hpG
  have hdvd : p ∣ G := Nat.dvd_of_mod_eq_zero hGp
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : 2 ≤ k := by
    by_contra hc
    have h1 : k < 2 := by omega
    interval_cases k
    · rw [Nat.mul_zero] at hk
      omega
    · rw [Nat.mul_one] at hk
      omega
  have h2p : p + p ≤ G := by
    rw [hk]
    calc p + p = p * 2 := by ring
      _ ≤ p * k := Nat.mul_le_mul_left p hk2
  intro i j hi hj hagree
  by_contra hne
  have hiG : i < G := by omega
  have hjG : j < G := by omega
  have hipG : i + p < G := by omega
  have mi : i % G = i := Nat.mod_eq_of_lt hiG
  have mj : j % G = j := Nat.mod_eq_of_lt hjG
  have mip : (i + p) % G = i + p := Nat.mod_eq_of_lt hipG
  have hdist : i % G ≠ j % G ∧ j % G ≠ (i + p) % G ∧
      i % G ≠ (i + p) % G := by
    rw [mi, mj, mip]
    exact ⟨hne, by omega, by omega⟩
  -- The initial triple: `j` agrees with `i` by hypothesis and with
  -- `i + p` by `p`-periodicity.
  have hag0 : TripleAgree hG S i j (i + p) (L - 1) := by
    intro d hd
    have h1 := hagree d hd
    have h2 := hper (i + d)
    have heq : (i + d) + p = (i + p) + d := by omega
    rw [heq] at h2
    exact ⟨h1, h1.symm.trans h2⟩
  exact extend_triple hG S hL i j (i + p) hdist hag0 hno
    (fun b₁ b₂ ℓ hne2 hle2 hag2 b hbG e₁ e₂ => by
      have hpℓ : p ≤ ℓ := le_trans hple hle2
      -- The escape pair is a uniform back-shift of `(i, j)`, hence
      -- still distinct mod `p`.
      have hmodp : b₁ % p ≠ b₂ % p := by
        rw [e₁, e₂]
        have hC : i + G - b = i + (G - b) := by omega
        have hC2 : j + G - b = j + (G - b) := by omega
        rw [hC, hC2]
        intro hcon
        apply hne
        have hme : i ≡ j [MOD p] :=
          Nat.ModEq.add_right_cancel' (G - b) hcon
        have ei : i % p = i := Nat.mod_eq_of_lt hi
        have ej : j % p = j := Nat.mod_eq_of_lt hj
        have hij : i = j := by
          rw [← ei, ← ej]
          exact hme
        exact hij
      obtain ⟨s, hs0, hsp, hsper⟩ :=
        small_period_of_ge_p_agree hG S p hp0 hper b₁ b₂ ℓ hmodp hpℓ hag2
      exact hsmall s hs0 hsp hsper)

/-- **Periodic cycle shape.** Periodicity plus distinctness of the
period's length-`(L-1)` windows (`hNwin` — the kernel-checked Lemma-C
consequence `periodic_factor_distinct`) give the simple directed-cycle
shape. The out-edge argument consumes `hNwin` (shared prefixes force
equal residues), and the in-edge argument consumes `hNwin` on starts
shifted by one (shared suffixes force equal residues). -/
theorem periodic_cycle_shape {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) (S : Fin G → α) (p : ℕ) (hp0 : 0 < p) (hple : p ≤ G)
    (hper : IsPeriod hG S p)
    (hNwin : ∀ i j : ℕ, i < p → j < p →
      (∀ d : ℕ, d < L - 1 → OrientedRigidity.cyc hG S (i + d) =
        OrientedRigidity.cyc hG S (j + d)) → i = j) :
    IsSimpleCycle L hG S := by
  constructor
  · -- Out-edges: shared prefixes force equal residues via `hNwin`.
    intro k hk
    simp only [OrientedRigidity.genomeNodes, Finset.mem_image] at hk
    obtain ⟨t, _, rfl⟩ := hk
    obtain ⟨r, hrp, hreq⟩ := nodeWindow_residue hG S p hp0 hple hper t
    have hrS : OrientedRigidity.window (L := L) hG S r ∈
        OrientedRigidity.support (L := L) hG S :=
      Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
    have hrc : OrientedRigidity.winPrefix (OrientedRigidity.window (L := L) hG S r) =
        OrientedRigidity.nodeWindow (L := L) hG S t := by
      rw [pre_window]
      exact hreq.symm
    refine ⟨OrientedRigidity.window hG S r, ⟨hrS, hrc⟩, ?_⟩
    intro w hw
    obtain ⟨hwS, hwpre⟩ := hw
    simp only [OrientedRigidity.support, Finset.mem_image] at hwS
    obtain ⟨u, _, rfl⟩ := hwS
    obtain ⟨r', hr'p, hreq'⟩ := window_residue hG S p hp0 hple hper u
    have hNW : OrientedRigidity.nodeWindow (L := L) hG S r' =
        OrientedRigidity.nodeWindow (L := L) hG S r := by
      have e1 : OrientedRigidity.winPrefix (OrientedRigidity.window (L := L) hG S r') =
          OrientedRigidity.nodeWindow (L := L) hG S r' := pre_window hG S r'
      -- Goal `nodeWindow r' = nodeWindow r`: unfold the left side to the
      -- prefix of `window r'`, transport to `window u`, then use `hwpre`.
      rw [← e1, ← hreq', hwpre]
      exact hreq
    have hrr : r'.val = r.val := by
      apply hNwin r'.val r.val hr'p hrp
      intro d hd
      have h := congrFun hNW ⟨d, hd⟩
      exact h
    have hrrF : r' = r := Fin.ext hrr
    rw [hreq', hrrF]
  · -- In-edges: the center is the window one residue-step back.
    intro k hk
    simp only [OrientedRigidity.genomeNodes, Finset.mem_image] at hk
    obtain ⟨t, _, rfl⟩ := hk
    -- Residue one step back: `ρ = (t % p + p - 1) % p`, a valid `Fin G`
    -- since `ρ < p ≤ G`.
    have hρG : (t.val % p + p - 1) % p < G :=
      lt_of_lt_of_le (Nat.mod_lt _ hp0) hple
    set ρ : Fin G := ⟨(t.val % p + p - 1) % p, hρG⟩ with hρ
    have hρval : ρ.val = (t.val % p + p - 1) % p := rfl
    have hρltp : ρ.val < p := by
      rw [hρval]
      exact Nat.mod_lt _ hp0
    have hρback : (ρ.val + 1) % p = t.val % p := by
      rw [hρval]
      exact back_step_residue t.val p hp0
    have hrS : OrientedRigidity.window (L := L) hG S ρ ∈
        OrientedRigidity.support (L := L) hG S :=
      Finset.mem_image.mpr ⟨ρ, Finset.mem_univ _, rfl⟩
    -- The suffix of the back-step window is the node window at `t`:
    -- `(ρ + (d+1)) % p = (t + d) % p` by the back-step identity.
    have hrc : OrientedRigidity.winSuffix (OrientedRigidity.window (L := L) hG S ρ) =
        OrientedRigidity.nodeWindow (L := L) hG S t := by
      rw [suf_window]
      funext d
      show OrientedRigidity.cyc hG S (ρ.val + (d.val + 1)) =
        OrientedRigidity.nodeWindow hG S t d
      have hmod : (ρ.val + (d.val + 1)) % p = (t.val + d.val) % p := by
        have e1 : (ρ.val + (d.val + 1)) % p = ((ρ.val + 1) + d.val) % p := by
          congr 1
          omega
        have e2 : ((ρ.val + 1) + d.val) % p =
            (((ρ.val + 1) % p) + d.val) % p := by
          rw [Nat.mod_add_mod]
        have e3 : (t.val + d.val) % p = ((t.val % p) + d.val) % p := by
          rw [Nat.mod_add_mod]
        rw [e1, e2, hρback, e3]
      have lhs : OrientedRigidity.cyc hG S (ρ.val + (d.val + 1)) =
          OrientedRigidity.cyc hG S (t.val + d.val) :=
        cyc_per_congr hG S p hper hmod
      have rhs : OrientedRigidity.nodeWindow hG S t d =
          OrientedRigidity.cyc hG S (t.val + d.val) := rfl
      rw [rhs]
      exact lhs
    refine ⟨OrientedRigidity.window hG S ρ, ⟨hrS, hrc⟩, ?_⟩
    intro w hw
    obtain ⟨hwS, hwpre⟩ := hw
    simp only [OrientedRigidity.support, Finset.mem_image] at hwS
    obtain ⟨u, _, rfl⟩ := hwS
    obtain ⟨r', hr'p, hreq'⟩ := window_residue hG S p hp0 hple hper u
    have hwpre' : OrientedRigidity.winSuffix
        (OrientedRigidity.window (L := L) hG S r') =
        OrientedRigidity.nodeWindow (L := L) hG S t := by
      rw [← hreq']
      exact hwpre
    have hsufEq : (fun d : Fin (L - 1) =>
            OrientedRigidity.cyc hG S (r'.val + (d.val + 1))) =
          OrientedRigidity.nodeWindow (L := L) hG S t := by
      rw [← suf_window hG S r']
      exact hwpre'
    -- Suffix agreement between the shifted residues `(r'+1) % p`, `t % p`.
    have hshift : (r'.val + 1) % p = t.val % p := by
      apply hNwin ((r'.val + 1) % p) (t.val % p)
        (Nat.mod_lt _ hp0) (Nat.mod_lt _ hp0)
      intro d hd
      have lhs : OrientedRigidity.cyc hG S (((r'.val + 1) % p) + d) =
          OrientedRigidity.cyc hG S (r'.val + (d + 1)) := by
        apply cyc_per_congr hG S p hper
        have e1 : (((r'.val + 1) % p) + d) % p =
            ((r'.val + 1) + d) % p := by
          rw [Nat.mod_add_mod]
        have e2 : (r'.val + (d + 1)) % p = ((r'.val + 1) + d) % p := by
          congr 1
          omega
        rw [e1, e2]
      have mid : OrientedRigidity.cyc hG S (r'.val + (d + 1)) =
          OrientedRigidity.cyc hG S (t.val % p + d) := by
        have h := congrFun hsufEq ⟨d, hd⟩
        have hrhs : OrientedRigidity.nodeWindow hG S t ⟨d, hd⟩ =
            OrientedRigidity.cyc hG S (t.val % p + d) := by
          have e := (cyc_residue_add hG S p hper t.val d).symm
          show OrientedRigidity.cyc hG S (t.val + d) = _
          exact e.symm
        rw [hrhs] at h
        exact h
      rw [lhs]
      exact mid
    -- Recover `r' = ρ`: the `+1`-shift is injective on residues below `p`.
    have hrr : r'.val = ρ.val := by
      have h1 : (r'.val + 1) % p = (ρ.val + 1) % p := by
        rw [hρback]
        exact hshift
      have hr'p1 : r'.val + 1 ≤ p := by omega
      have hρp1 : ρ.val + 1 ≤ p := by omega
      by_cases h1lt : r'.val + 1 < p
      · by_cases h2lt : ρ.val + 1 < p
        · rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt h2lt] at h1
          omega
        · have eρ : ρ.val + 1 = p := by omega
          rw [Nat.mod_eq_of_lt h1lt, eρ, Nat.mod_self] at h1
          omega
      · have er' : r'.val + 1 = p := by omega
        by_cases h2lt : ρ.val + 1 < p
        · rw [er', Nat.mod_self, Nat.mod_eq_of_lt h2lt] at h1
          omega
        · have eρ : ρ.val + 1 = p := by omega
          omega
    have hrrF : r' = ρ := Fin.ext hrr
    rw [hreq', hrrF]

/-- **Periodic route end-to-end.** Under a minimal period, no long
triple repeat, and the BBT competitor inputs, every same-length spelled
candidate has exactly the truth's spectrum. The period-factor
distinctness feeding the cycle shape is the kernel-checked Lemma-C
consequence `periodic_factor_distinct` — not an external premise. The
minimality/divisibility parts of `hmin` are case-split context; the Lean
argument consumes the period bounds, the period itself, and `hno`. -/
theorem periodic_rigidity_same_spectrum {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) (S : Fin G → α) (p : ℕ)
    (hmin : HasMinimalPeriod hG S p)
    (hL : 2 ≤ L)
    (hno : ¬ HasLongTripleRepeat hG S L)
    (B : (Fin L → α) → ℕ)
    (hBsup : ∀ w, w ∈ OrientedRigidity.support hG S ↔ 0 < B w)
    (hBbal : OrientedRigidity.Balanced OrientedRigidity.winPrefix
      OrientedRigidity.winSuffix (OrientedRigidity.genomeNodes hG S)
      (OrientedRigidity.support hG S) B)
    (hBtot : ∑ w ∈ OrientedRigidity.support hG S, B w = G) :
    ∀ w, B w = OrientedRigidity.specCount hG S w := by
  obtain ⟨hp0, hpG, _hGp, hper, _hmin⟩ := hmin
  have hple : p ≤ G := le_of_lt hpG
  have hNwin : ∀ i j : ℕ, i < p → j < p →
      (∀ d : ℕ, d < L - 1 → OrientedRigidity.cyc hG S (i + d) =
        OrientedRigidity.cyc hG S (j + d)) → i = j :=
    periodic_factor_distinct hG S p hL ⟨hp0, hpG, _hGp, hper, _hmin⟩ hno
  have hcyc := periodic_cycle_shape hG S p hp0 hple hper hNwin
  have hmemT : ∀ w ∈ OrientedRigidity.support hG S,
      OrientedRigidity.winPrefix w ∈ OrientedRigidity.genomeNodes hG S ∧
        OrientedRigidity.winSuffix w ∈ OrientedRigidity.genomeNodes hG S :=
    OrientedRigidity.mem_nodes_of_mem_support (L := L) hG S
  have hApos : ∀ w ∈ OrientedRigidity.support hG S,
      1 ≤ OrientedRigidity.specCount hG S w :=
    OrientedRigidity.truth_pos_on_support (L := L) hG S
  have hBpos : ∀ w ∈ OrientedRigidity.support hG S, 1 ≤ B w :=
    fun w hw => (hBsup w).mp hw
  have hAbal' : ∀ v ∈ OrientedRigidity.genomeNodes hG S,
      ∑ e ∈ (OrientedRigidity.support hG S).filter
          (fun e => OrientedRigidity.winPrefix e = v),
        OrientedRigidity.specCount hG S e =
      ∑ e ∈ (OrientedRigidity.support hG S).filter
          (fun e => OrientedRigidity.winSuffix e = v),
        OrientedRigidity.specCount hG S e :=
    OrientedRigidity.truth_balanced (L := L) hG S
  have hBbal' : ∀ v ∈ OrientedRigidity.genomeNodes hG S,
      ∑ e ∈ (OrientedRigidity.support hG S).filter
          (fun e => OrientedRigidity.winPrefix e = v), B e =
      ∑ e ∈ (OrientedRigidity.support hG S).filter
          (fun e => OrientedRigidity.winSuffix e = v), B e := hBbal
  have hAtot := OrientedRigidity.truth_total (L := L) hG S
  have hstrong := OrientedRigidity.truth_strongly_connected (L := L) hG S
  have hne := support_nonempty (L := L) hG S
  have heq := unique_circulation_of_cycle OrientedRigidity.winPrefix
    OrientedRigidity.winSuffix (OrientedRigidity.genomeNodes hG S)
    (OrientedRigidity.support hG S)
    (OrientedRigidity.specCount hG S) B
    hmemT hApos hBpos hAbal' hBbal' (hAtot.trans hBtot.symm)
    hcyc.1 hcyc.2 hstrong hne
  intro w
  by_cases hw : w ∈ OrientedRigidity.support hG S
  · exact (heq w hw).symm
  · have hB0 : B w = 0 :=
      Nat.eq_zero_of_not_pos (fun h => hw ((hBsup w).mpr h))
    have hA0 : OrientedRigidity.specCount hG S w = 0 := by
      have hemp : Finset.univ.filter
          (fun r : Fin G => OrientedRigidity.window hG S r = w) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro r hr
        apply hw
        have hwr : OrientedRigidity.window hG S r = w :=
          (Finset.mem_filter.mp hr).2
        rw [← hwr]
        exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
      show (Finset.univ.filter
        (fun r : Fin G => OrientedRigidity.window hG S r = w)).card = 0
      rw [hemp, Finset.card_empty]
    rw [hB0, hA0]

end AssemblyP1.RepeatAdapter
