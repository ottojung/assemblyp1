import Mathlib

set_option linter.unusedSectionVars false

/-!
# Graver rigidity criterion (issue #264)

This file formalizes a DIRECT Lean proof of the Graver-basis rigidity
criterion for same-length positive integer-flow rigidity: the conformal
certificate form of Theorem 1 of `ExactRigidityCriterion.lean`, §2 of
`docs/source-notes/issue-257-rigid-read-graphs.md`.

> Let `E` be a finite type of support edges, `A : E → ℤ` a positive balanced
> circulation of total `G` on the support, and `L₀ = ker_ℤ[M; 1ᵀ] ∩ ℤ^E` the
> lattice of zero-sum integer circulations (signed/oriented vertex balance
> plus the fixed-total row). The **Graver basis** `Gr(M)` is the set of
> conformally indecomposable nonzero elements of `L₀`. Then `A` is rigid
> **iff** no Graver element `g` satisfies `g ≥ 1 - A` coordinatewise
> (equivalently, `A + g` is not feasible).

## Main result

`rigid_iff_forall_graver_not_feasible` proves, directly in the kernel (without
passing through `ExactRigidityCriterion.nonrigid_iff_exists_delta`):

```
Rigid A G  ↔  ∀ g, Graver g → ¬ Feasible (A + g)
```

where `Feasible B` means `B ≥ 1` (box lower bound), `B` balanced, and
`∑ B = G` (fixed total mass). Since a Graver element is balanced and
zero-sum, `Feasible (A + g)` is exactly the box condition `g ≥ 1 - A`;
`rigid_iff_forall_graver_not_inbox` states the criterion in that form.

## Proof structure

* `Graver` includes `BalancedZ`/`ZeroSum` of `g` in the predicate (the
  blocking-review correction over the earlier WIP), and the edge type `E` is
  the support itself (a subtype of graph edges), so there are no off-support
  ghost coordinates. All section parameters (`tail head nodes`) are passed
  explicitly; `#check @Graver` shows them.
* `exists_graver_conformal`: the key lemma. For every nonzero `δ ∈ L₀` there
  is a nonzero Graver `g` with `g ⊑ δ` (sign-conformal). Proof: strong
  induction on the l1 norm `∑ |δ_e|` — the same minimization as choosing the
  l1-minimal nonzero kernel element inside the finite box
  `∏_e [-|δ_e|, |δ_e|]` (finite because `E` is a `Fintype`; Dickson's lemma
  gives the finiteness of the whole Graver basis). If `δ` is conformally
  indecomposable we are done; otherwise `δ = g₁ + g₂` with `g₁, g₂ ∈ L₀`
  conformally below `δ` and both nonzero, and the l1 norm (additive under
  conformal decomposition) strictly decreases, so the induction hypothesis
  applies to `g₁`.
* `graver_decomposition` (for issue #263): every nonzero `δ ∈ L₀` is a sum of
  sign-compatible Graver elements, by the same l1 induction.
* (⟸) of the main iff: an alternate feasible `B` gives `δ = B - A ∈ L₀`
  inside the box; the key lemma produces a nonzero Graver `g ⊑ δ`, and
  `A + g` lies pointwise between `A` and `B`, hence feasible — contradiction.
  (⟹): a feasible `A + g` with Graver `g ≠ 0` is itself an alternate
  circulation.

## References

* Eisenbrand, Weismantel, et al., *Proximity results and faster algorithms
  for integer programming*, arXiv:1904.01361.
* Hemmecke, Onn, Weismantel, *A polynomial oracle-time algorithm for convex
  integer minimization*, arXiv:0710.3003; Mathematical Programming 126 (2011),
  97–117.
* Hunkenschröder, Koutecký, Levin, Vu, *(Near)-Optimal algorithms for sparse
  separable convex integer programs*, Mathematical Programming (2026),
  Proposition 3 (Positive Sum Property),
  https://link.springer.com/article/10.1007/s10107-026-02341-5.

## Open

* The finiteness of the full Graver basis (Dickson's lemma) is not
  formalized; only the single l1-minimal witness extraction is.
* The discharge of #263's conditional convex optimality theorem from
  `graver_decomposition` is left to that front.
-/

namespace AssemblyP1.GraverRigidity

open Finset
open BigOperators

section GraverBasis

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype E]

/-- Out-edges of `v` within the support (all of `E`). -/
private def outF (tail : E → V) (v : V) : Finset E :=
  Finset.univ.filter (fun e => tail e = v)

/-- In-edges of `v` within the support (all of `E`). -/
private def inF (head : E → V) (v : V) : Finset E :=
  Finset.univ.filter (fun e => head e = v)

/-- Balance at every node over `ℤ`: the signed/oriented vertex-balance rows
`M f = 0` of the integer incidence matrix. -/
def BalancedZ (tail head : E → V) (nodes : Finset V) (f : E → ℤ) : Prop :=
  ∀ v ∈ nodes, ∑ e ∈ outF tail v, f e = ∑ e ∈ inF head v, f e

/-- Zero total sum over `ℤ`: the fixed-total row `1ᵀ f = 0` of the integer
incidence matrix. Together `BalancedZ` + `ZeroSum` define the lattice
`L₀ = ker_ℤ[M; 1ᵀ] ∩ ℤ^E`. -/
def ZeroSum (f : E → ℤ) : Prop :=
  ∑ e ∈ Finset.univ, f e = 0

/-- Positivity over `ℤ`: the box lower bound `f ≥ 1`. -/
def Pos (f : E → ℤ) : Prop :=
  ∀ e, (1 : ℤ) ≤ f e

/-- `A` is rigid: it is the only positive balanced integer circulation of
total `G` on the support `E`. -/
def Rigid (tail head : E → V) (nodes : Finset V) (A : E → ℤ) (G : ℕ) : Prop :=
  ∀ B : E → ℤ, Pos B → BalancedZ tail head nodes B →
    (∑ e ∈ Finset.univ, B e = G) → B = A

/-- A circulation is feasible for total `G`: positive (box lower bound `1`),
balanced, and of total mass `G`. The per-edge upper bound `G - (|E| - 1)` is
derived from the same mass constraint. -/
def Feasible (tail head : E → V) (nodes : Finset V) (G : ℕ) (B : E → ℤ) : Prop :=
  Pos B ∧ BalancedZ tail head nodes B ∧ (∑ e ∈ Finset.univ, B e = G)

/-- Positive part of an integer vector (function coordinate). -/
def posPart (f : E → ℤ) : E → ℤ := fun e => max (f e) 0

/-- Negative part of an integer vector (function coordinate). -/
def negPart (f : E → ℤ) : E → ℤ := fun e => max (-(f e)) 0

/-- The sign-conformal order: `g₁ ⊑ g₂` iff the positive and negative parts of
`g₁` are coordinatewise bounded by those of `g₂`. -/
def Conformal (g₁ g₂ : E → ℤ) : Prop :=
  ∀ e, negPart g₁ e ≤ negPart g₂ e ∧ posPart g₁ e ≤ posPart g₂ e

/-- The l1 norm of an integer vector. -/
def l1Norm (f : E → ℤ) : ℕ := ∑ e ∈ Finset.univ, Int.natAbs (f e)

/-- The box condition: `g ≥ 1 - A` coordinatewise. -/
def InBox (A : E → ℤ) (g : E → ℤ) : Prop :=
  ∀ e, (1 - A e) ≤ g e

/-- The Graver basis predicate: `g` is Graver iff it is a nonzero element of
the lattice `L₀ = ker_ℤ[M; 1ᵀ]` (so `BalancedZ` and `ZeroSum` hold of `g`
itself — the blocking-review correction) and every sign-compatible
decomposition `g = g₁ + g₂` with `g₁, g₂ ∈ L₀` is trivial. -/
def Graver (tail head : E → V) (nodes : Finset V) (g : E → ℤ) : Prop :=
  (∃ e, g e ≠ 0) ∧ BalancedZ tail head nodes g ∧ ZeroSum g ∧
    ∀ g₁ g₂ : E → ℤ,
      BalancedZ tail head nodes g₁ → ZeroSum g₁ →
      BalancedZ tail head nodes g₂ → ZeroSum g₂ →
      Conformal g₁ g → Conformal g₂ g → g = g₁ + g₂ → g₁ = 0 ∨ g₂ = 0

theorem posPart_sub_negPart {f : E → ℤ} (e : E) : f e = posPart f e - negPart f e := by
  unfold posPart negPart
  rcases le_total (f e) 0 with h | h
  · rw [max_eq_right h, max_eq_left (by omega)]
    omega
  · rw [max_eq_left h, max_eq_right (by omega)]
    omega

theorem posPart_nonneg {f : E → ℤ} (e : E) : (0 : ℤ) ≤ posPart f e := by
  unfold posPart
  exact le_max_right (f e) 0

theorem negPart_nonneg {f : E → ℤ} (e : E) : (0 : ℤ) ≤ negPart f e := by
  unfold negPart
  exact le_max_right (-(f e)) 0

theorem posPart_eq_zero_of_nonpos {f : E → ℤ} {e : E} (h : f e ≤ 0) : posPart f e = 0 := by
  unfold posPart
  exact max_eq_right h

theorem negPart_eq_zero_of_nonneg {f : E → ℤ} {e : E} (h : 0 ≤ f e) : negPart f e = 0 := by
  unfold negPart
  exact max_eq_right (by omega)

theorem posPart_eq_zero {f : E → ℤ} {e : E} (h : posPart f e = 0) : f e ≤ 0 := by
  unfold posPart at h
  omega

theorem negPart_eq_zero {f : E → ℤ} {e : E} (h : negPart f e = 0) : (0 : ℤ) ≤ f e := by
  unfold negPart at h
  omega

theorem natAbs_of_nonpos {x : ℤ} (h : x ≤ 0) : (Int.natAbs x : ℤ) = -x := by
  have h1 : (Int.natAbs x : ℤ) = (Int.natAbs (-x) : ℤ) := by rw [Int.natAbs_neg]
  have h2 : (Int.natAbs (-x) : ℤ) = -x := Int.natAbs_of_nonneg (by omega)
  omega

theorem abs_eq_epos_add_eneg (δ : E → ℤ) (e : E) :
    ((Int.natAbs (δ e) : ℤ)) = posPart δ e + negPart δ e := by
  unfold posPart negPart
  rcases le_total (δ e) 0 with h | h
  · rw [natAbs_of_nonpos h, max_eq_right h, max_eq_left (by omega)]
    omega
  · rw [Int.natAbs_of_nonneg h, max_eq_left h, max_eq_right (by omega)]
    omega

theorem Conformal.refl (g : E → ℤ) : Conformal g g :=
  fun _ => ⟨le_refl _, le_refl _⟩

theorem Conformal.trans {g₁ g₂ g₃ : E → ℤ} (h₁ : Conformal g₁ g₂)
    (h₂ : Conformal g₂ g₃) : Conformal g₁ g₃ :=
  fun e => ⟨le_trans (h₁ e).1 (h₂ e).1, le_trans (h₁ e).2 (h₂ e).2⟩

theorem BalancedZ.add (tail head : E → V) (nodes : Finset V) {f g : E → ℤ}
    (hf : BalancedZ tail head nodes f) (hg : BalancedZ tail head nodes g) :
    BalancedZ tail head nodes (f + g) := by
  intro v hv
  have h1 := hf v hv
  have h2 := hg v hv
  show ∑ e ∈ outF tail v, (f e + g e) = ∑ e ∈ inF head v, (f e + g e)
  simp only [Finset.sum_add_distrib]
  omega

theorem BalancedZ.sub (tail head : E → V) (nodes : Finset V) {f g : E → ℤ}
    (hf : BalancedZ tail head nodes f) (hg : BalancedZ tail head nodes g) :
    BalancedZ tail head nodes (f - g) := by
  intro v hv
  have h1 := hf v hv
  have h2 := hg v hv
  show ∑ e ∈ outF tail v, (f e - g e) = ∑ e ∈ inF head v, (f e - g e)
  simp only [Finset.sum_sub_distrib]
  omega

theorem ZeroSum.add {f g : E → ℤ} (hf : ZeroSum f) (hg : ZeroSum g) :
    ZeroSum (f + g) := by
  have h1 : ∑ e ∈ Finset.univ, f e = 0 := hf
  have h2 : ∑ e ∈ Finset.univ, g e = 0 := hg
  show ∑ e ∈ Finset.univ, (f e + g e) = 0
  simp only [Finset.sum_add_distrib]
  omega

theorem ZeroSum.sub {f g : E → ℤ} (hf : ZeroSum f) (hg : ZeroSum g) :
    ZeroSum (f - g) := by
  have h1 : ∑ e ∈ Finset.univ, f e = 0 := hf
  have h2 : ∑ e ∈ Finset.univ, g e = 0 := hg
  show ∑ e ∈ Finset.univ, (f e - g e) = 0
  simp only [Finset.sum_sub_distrib]
  omega

theorem inbox_of_conformal {A g δ : E → ℤ} (hg : Conformal g δ)
    (hδ : InBox A δ) (hA : Pos A) : InBox A g := by
  intro e
  have h1 : (1 : ℤ) ≤ A e := hA e
  have h2 : (1 - A e) ≤ δ e := hδ e
  rcases le_total 0 (δ e) with h | h
  · have h3 : negPart g e ≤ negPart δ e := (hg e).1
    have h4 : negPart δ e = 0 := negPart_eq_zero_of_nonneg h
    rw [h4] at h3
    have h5 : (0 : ℤ) ≤ g e := negPart_eq_zero (le_antisymm h3 (negPart_nonneg e))
    omega
  · have h3 : posPart g e ≤ posPart δ e := (hg e).2
    have h4 : posPart δ e = 0 := posPart_eq_zero_of_nonpos h
    rw [h4] at h3
    have h5 : g e ≤ 0 := posPart_eq_zero (le_antisymm h3 (posPart_nonneg e))
    have h6 : negPart g e ≤ negPart δ e := (hg e).1
    have h7 : δ e = -negPart δ e := by
      have h0 : posPart δ e = 0 := posPart_eq_zero_of_nonpos h
      have h1 : δ e = posPart δ e - negPart δ e := posPart_sub_negPart e
      omega
    have h8 : g e = -negPart g e := by
      have h0 : posPart g e = 0 := le_antisymm h3 (posPart_nonneg e)
      have h1 : g e = posPart g e - negPart g e := posPart_sub_negPart e
      omega
    omega

theorem pos_add_of_inbox {A g : E → ℤ} (hg : InBox A g) (hA : Pos A) :
    Pos (A + g) := by
  intro e
  have h1 : (1 : ℤ) ≤ A e := hA e
  have h2 : (1 - A e) ≤ g e := hg e
  show (1 : ℤ) ≤ A e + g e
  omega

theorem natAbs_add_of_conformal {g₁ g₂ : E → ℤ} (h₁ : Conformal g₁ (g₁ + g₂))
    (h₂ : Conformal g₂ (g₁ + g₂)) (e : E) :
    Int.natAbs ((g₁ + g₂) e) = Int.natAbs (g₁ e) + Int.natAbs (g₂ e) := by
  rcases le_total 0 (g₁ e + g₂ e) with hge | hle
  · have hn : negPart (g₁ + g₂) e = 0 := negPart_eq_zero_of_nonneg hge
    have h' : negPart g₁ e ≤ negPart (g₁ + g₂) e := (h₁ e).1
    rw [hn] at h'
    have hp₁ : (0 : ℤ) ≤ g₁ e := negPart_eq_zero (le_antisymm h' (negPart_nonneg e))
    have h'₂ : negPart g₂ e ≤ negPart (g₁ + g₂) e := (h₂ e).1
    rw [hn] at h'₂
    have hp₂ : (0 : ℤ) ≤ g₂ e := negPart_eq_zero (le_antisymm h'₂ (negPart_nonneg e))
    exact_mod_cast (by
      have e1 : ((Int.natAbs ((g₁ + g₂) e) : ℕ) : ℤ) = g₁ e + g₂ e :=
        Int.natAbs_of_nonneg hge
      have e2 : ((Int.natAbs (g₁ e) : ℕ) : ℤ) = g₁ e := Int.natAbs_of_nonneg hp₁
      have e3 : ((Int.natAbs (g₂ e) : ℕ) : ℤ) = g₂ e := Int.natAbs_of_nonneg hp₂
      omega)
  · have hp : posPart (g₁ + g₂) e = 0 := posPart_eq_zero_of_nonpos hle
    have h' : posPart g₁ e ≤ posPart (g₁ + g₂) e := (h₁ e).2
    rw [hp] at h'
    have hn₁ : g₁ e ≤ 0 := posPart_eq_zero (le_antisymm h' (posPart_nonneg e))
    have h'₂ : posPart g₂ e ≤ posPart (g₁ + g₂) e := (h₂ e).2
    rw [hp] at h'₂
    have hn₂ : g₂ e ≤ 0 := posPart_eq_zero (le_antisymm h'₂ (posPart_nonneg e))
    exact_mod_cast (by
      have e1 : ((Int.natAbs ((g₁ + g₂) e) : ℕ) : ℤ) = -(g₁ e + g₂ e) :=
        natAbs_of_nonpos hle
      have e2 : ((Int.natAbs (g₁ e) : ℕ) : ℤ) = -g₁ e := natAbs_of_nonpos hn₁
      have e3 : ((Int.natAbs (g₂ e) : ℕ) : ℤ) = -g₂ e := natAbs_of_nonpos hn₂
      omega)

theorem l1Norm_add_of_conformal {g₁ g₂ : E → ℤ} (h₁ : Conformal g₁ (g₁ + g₂))
    (h₂ : Conformal g₂ (g₁ + g₂)) : l1Norm (g₁ + g₂) = l1Norm g₁ + l1Norm g₂ := by
  show (∑ e ∈ Finset.univ, Int.natAbs ((g₁ + g₂) e))
      = (∑ e ∈ Finset.univ, Int.natAbs (g₁ e)) + (∑ e ∈ Finset.univ, Int.natAbs (g₂ e))
  calc (∑ e ∈ Finset.univ, Int.natAbs ((g₁ + g₂) e))
      = ∑ e ∈ Finset.univ, (Int.natAbs (g₁ e) + Int.natAbs (g₂ e)) :=
        Finset.sum_congr rfl (fun e _ => natAbs_add_of_conformal h₁ h₂ e)
    _ = (∑ e ∈ Finset.univ, Int.natAbs (g₁ e)) + (∑ e ∈ Finset.univ, Int.natAbs (g₂ e)) :=
        Finset.sum_add_distrib

theorem l1Norm_pos_of_ne {f : E → ℤ} (hne : ∃ e, f e ≠ 0) : 0 < l1Norm f := by
  obtain ⟨e₀, he₀⟩ := hne
  have h1 : (0 : ℕ) < Int.natAbs (f e₀) := Int.natAbs_pos.2 he₀
  have h2 : (Int.natAbs (f e₀) : ℕ) ≤ l1Norm f := by
    show (Int.natAbs (f e₀) : ℕ) ≤ ∑ e ∈ Finset.univ, Int.natAbs (f e)
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (Int.natAbs (f i))) (Finset.mem_univ e₀)
  omega

theorem conformal_mem_box {g δ : E → ℤ} (h : Conformal g δ) (e : E) :
    -Int.natAbs (δ e) ≤ g e ∧ g e ≤ Int.natAbs (δ e) := by
  have h1 : posPart g e ≤ posPart δ e := (h e).2
  have h2 : negPart g e ≤ negPart δ e := (h e).1
  have h3 : (Int.natAbs (δ e) : ℤ) = posPart δ e + negPart δ e :=
    abs_eq_epos_add_eneg δ e
  have h4 : g e = posPart g e - negPart g e := posPart_sub_negPart e
  have h5 : (0 : ℤ) ≤ posPart g e := posPart_nonneg e
  have h6 : (0 : ℤ) ≤ negPart g e := negPart_nonneg e
  have h7 : (0 : ℤ) ≤ posPart δ e := posPart_nonneg e
  have h8 : (0 : ℤ) ≤ negPart δ e := negPart_nonneg e
  constructor <;> omega

/-- **Key lemma.** Every nonzero lattice vector `δ ∈ L₀` has a nonzero Graver
element `g` sign-conformally below it (`g ⊑ δ`). This is the l1-minimal
witness inside the finite box `∏_e [-|δ_e|, |δ_e|]`. -/
theorem exists_graver_conformal_aux (tail head : E → V) (nodes : Finset V) :
    ∀ (n : ℕ) (δ : E → ℤ),
    l1Norm δ = n → BalancedZ tail head nodes δ → ZeroSum δ → (∃ e, δ e ≠ 0) →
    ∃ g : E → ℤ, Graver tail head nodes g ∧ Conformal g δ ∧ ∃ e, g e ≠ 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro δ hn hbal hsum hne
    by_cases hG : Graver tail head nodes δ
    · exact ⟨δ, hG, Conformal.refl δ, hne⟩
    · -- `δ` is nonzero, balanced and zero-sum, so failing `Graver` means it
      -- admits a nontrivial conformal decomposition.
      have hdec : ∃ g₁ g₂ : E → ℤ,
          BalancedZ tail head nodes g₁ ∧ ZeroSum g₁ ∧
          BalancedZ tail head nodes g₂ ∧ ZeroSum g₂ ∧
          Conformal g₁ δ ∧ Conformal g₂ δ ∧ δ = g₁ + g₂ ∧ g₁ ≠ 0 ∧ g₂ ≠ 0 := by
        by_contra hcon
        apply hG
        refine ⟨hne, hbal, hsum, ?_⟩
        intro g₁ g₂ hbal₁ hsum₁ hbal₂ hsum₂ hc₁ hc₂ hde
        by_contra hne'
        apply hcon
        refine ⟨g₁, g₂, hbal₁, hsum₁, hbal₂, hsum₂, hc₁, hc₂, hde, ?_, ?_⟩
        · intro h0
          exact hne' (Or.inl h0)
        · intro h0
          exact hne' (Or.inr h0)
      obtain ⟨g₁, g₂, hbal₁, hsum₁, hbal₂, hsum₂, hc₁, hc₂, hde, hne₁, hne₂⟩ := hdec
      have hne₁' : ∃ e, g₁ e ≠ 0 := by
        by_contra hcon
        apply hne₁
        ext e
        by_contra h'
        exact hcon ⟨e, h'⟩
      have hne₂' : ∃ e, g₂ e ≠ 0 := by
        by_contra hcon
        apply hne₂
        ext e
        by_contra h'
        exact hcon ⟨e, h'⟩
      have hc₁s : Conformal g₁ (g₁ + g₂) := by rw [← hde]; exact hc₁
      have hc₂s : Conformal g₂ (g₁ + g₂) := by rw [← hde]; exact hc₂
      have hlt : l1Norm g₁ < n := by
        have hadd : l1Norm δ = l1Norm g₁ + l1Norm g₂ := by
          rw [hde]
          exact l1Norm_add_of_conformal hc₁s hc₂s
        have hpos : 0 < l1Norm g₂ := l1Norm_pos_of_ne hne₂'
        omega
      obtain ⟨g, hg, hg₁, hgne⟩ := ih (l1Norm g₁) hlt g₁ rfl hbal₁ hsum₁ hne₁'
      exact ⟨g, hg, Conformal.trans hg₁ hc₁, hgne⟩

theorem exists_graver_conformal (tail head : E → V) (nodes : Finset V) {δ : E → ℤ}
    (hbal : BalancedZ tail head nodes δ) (hsum : ZeroSum δ) (hne : ∃ e, δ e ≠ 0) :
    ∃ g : E → ℤ, Graver tail head nodes g ∧ Conformal g δ ∧ ∃ e, g e ≠ 0 :=
  exists_graver_conformal_aux tail head nodes (l1Norm δ) δ rfl hbal hsum hne

/-- **Graver conformal-decomposition theorem** (for issue #263): every
nonzero `δ ∈ L₀` is a sum of sign-compatible Graver elements. -/
theorem graver_decomposition_aux (tail head : E → V) (nodes : Finset V) :
    ∀ (n : ℕ) (δ : E → ℤ),
    l1Norm δ = n → BalancedZ tail head nodes δ → ZeroSum δ → (∃ e, δ e ≠ 0) →
    ∃ gs : List (E → ℤ),
      (∀ g ∈ gs, Graver tail head nodes g ∧ Conformal g δ ∧ ∃ e, g e ≠ 0) ∧
      gs.sum = δ := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro δ hn hbal hsum hne
    by_cases hG : Graver tail head nodes δ
    · refine ⟨[δ], ?_, ?_⟩
      · intro g hg
        rw [List.mem_singleton] at hg
        rw [hg]
        exact ⟨hG, Conformal.refl δ, hne⟩
      · show [δ].sum = δ
        simp
    · have hdec : ∃ g₁ g₂ : E → ℤ,
          BalancedZ tail head nodes g₁ ∧ ZeroSum g₁ ∧
          BalancedZ tail head nodes g₂ ∧ ZeroSum g₂ ∧
          Conformal g₁ δ ∧ Conformal g₂ δ ∧ δ = g₁ + g₂ ∧ g₁ ≠ 0 ∧ g₂ ≠ 0 := by
        by_contra hcon
        apply hG
        refine ⟨hne, hbal, hsum, ?_⟩
        intro g₁ g₂ hbal₁ hsum₁ hbal₂ hsum₂ hc₁ hc₂ hde
        by_contra hne'
        apply hcon
        refine ⟨g₁, g₂, hbal₁, hsum₁, hbal₂, hsum₂, hc₁, hc₂, hde, ?_, ?_⟩
        · intro h0
          exact hne' (Or.inl h0)
        · intro h0
          exact hne' (Or.inr h0)
      obtain ⟨g₁, g₂, hbal₁, hsum₁, hbal₂, hsum₂, hc₁, hc₂, hde, hne₁, hne₂⟩ := hdec
      have hne₁' : ∃ e, g₁ e ≠ 0 := by
        by_contra hcon
        apply hne₁
        ext e
        by_contra h'
        exact hcon ⟨e, h'⟩
      have hne₂' : ∃ e, g₂ e ≠ 0 := by
        by_contra hcon
        apply hne₂
        ext e
        by_contra h'
        exact hcon ⟨e, h'⟩
      have hc₁s : Conformal g₁ (g₁ + g₂) := by rw [← hde]; exact hc₁
      have hc₂s : Conformal g₂ (g₁ + g₂) := by rw [← hde]; exact hc₂
      have hlt₁ : l1Norm g₁ < n := by
        have hadd : l1Norm δ = l1Norm g₁ + l1Norm g₂ := by
          rw [hde]
          exact l1Norm_add_of_conformal hc₁s hc₂s
        have hpos : 0 < l1Norm g₂ := l1Norm_pos_of_ne hne₂'
        omega
      have hlt₂ : l1Norm g₂ < n := by
        have hadd : l1Norm δ = l1Norm g₁ + l1Norm g₂ := by
          rw [hde]
          exact l1Norm_add_of_conformal hc₁s hc₂s
        have hpos : 0 < l1Norm g₁ := l1Norm_pos_of_ne hne₁'
        omega
      obtain ⟨gs₁, hgs₁, hgsum₁⟩ := ih (l1Norm g₁) hlt₁ g₁ rfl hbal₁ hsum₁ hne₁'
      obtain ⟨gs₂, hgs₂, hgsum₂⟩ := ih (l1Norm g₂) hlt₂ g₂ rfl hbal₂ hsum₂ hne₂'
      refine ⟨gs₁ ++ gs₂, ?_, ?_⟩
      · intro g hg
        rw [List.mem_append] at hg
        rcases hg with hg | hg
        · exact ⟨(hgs₁ g hg).1, Conformal.trans (hgs₁ g hg).2.1 hc₁, (hgs₁ g hg).2.2⟩
        · exact ⟨(hgs₂ g hg).1, Conformal.trans (hgs₂ g hg).2.1 hc₂, (hgs₂ g hg).2.2⟩
      · rw [List.sum_append, hgsum₁, hgsum₂]
        exact hde.symm

theorem graver_decomposition (tail head : E → V) (nodes : Finset V) {δ : E → ℤ}
    (hbal : BalancedZ tail head nodes δ) (hsum : ZeroSum δ) (hne : ∃ e, δ e ≠ 0) :
    ∃ gs : List (E → ℤ),
      (∀ g ∈ gs, Graver tail head nodes g ∧ Conformal g δ ∧ ∃ e, g e ≠ 0) ∧
      gs.sum = δ :=
  graver_decomposition_aux tail head nodes (l1Norm δ) δ rfl hbal hsum hne

/-- **Main theorem (Graver rigidity criterion, issue #264).** `A` is rigid
iff no Graver element `g` makes `A + g` feasible. -/
theorem rigid_iff_forall_graver_not_feasible (tail head : E → V) (nodes : Finset V)
    (A : E → ℤ) (G : ℕ) (hA : Feasible tail head nodes G A) :
    Rigid tail head nodes A G ↔
      ∀ g : E → ℤ, Graver tail head nodes g → ¬ Feasible tail head nodes G (A + g) := by
  constructor
  · intro hRig g hg hFeas
    have hAg : A + g = A := hRig (A + g) hFeas.1 hFeas.2.1 hFeas.2.2
    obtain ⟨e₀, he₀⟩ := hg.1
    have hge : g e₀ = 0 := by
      have h2 : A e₀ + g e₀ = A e₀ := congrArg (fun f => f e₀) hAg
      omega
    exact he₀ hge
  · intro hno
    unfold Rigid
    intro B hBpos hBbal hBtot
    by_contra hBne
    have hfa : ¬∀ e, B e = A e := by
      intro h
      apply hBne
      exact funext h
    obtain ⟨e₀, he₀⟩ := Classical.not_forall.mp hfa
    have hδbal : BalancedZ tail head nodes (B - A) :=
      BalancedZ.sub tail head nodes hBbal hA.2.1
    have hδsum : ZeroSum (B - A) := by
      have h1 : ∑ e ∈ Finset.univ, B e = G := hBtot
      have h2 : ∑ e ∈ Finset.univ, A e = G := hA.2.2
      show ∑ e ∈ Finset.univ, (B e - A e) = 0
      simp only [Finset.sum_sub_distrib]
      omega
    have hδbox : InBox A (B - A) := by
      intro e
      have h1 := hBpos e
      show (1 - A e) ≤ B e - A e
      omega
    have hδne : ∃ e, (B - A) e ≠ 0 := by
      refine ⟨e₀, ?_⟩
      show B e₀ - A e₀ ≠ 0
      omega
    obtain ⟨g, hg, hgδ, hgne⟩ :=
      exists_graver_conformal tail head nodes hδbal hδsum hδne
    refine hno g hg ⟨?_, ?_, ?_⟩
    · exact pos_add_of_inbox (inbox_of_conformal hgδ hδbox hA.1) hA.1
    · exact BalancedZ.add tail head nodes hA.2.1 hg.2.1
    · have h1 : ∑ e ∈ Finset.univ, A e = G := hA.2.2
      have h2 : ∑ e ∈ Finset.univ, g e = 0 := hg.2.2.1
      show ∑ e ∈ Finset.univ, (A e + g e) = G
      simp only [Finset.sum_add_distrib]
      omega

/-- **Graver rigidity criterion, box form.** `A` is rigid iff no Graver
element `g ∈ Gr(M)` satisfies `g ≥ 1 - A` coordinatewise. -/
theorem rigid_iff_forall_graver_not_inbox (tail head : E → V) (nodes : Finset V)
    (A : E → ℤ) (G : ℕ) (hA : Feasible tail head nodes G A) :
    Rigid tail head nodes A G ↔
      ∀ g : E → ℤ, Graver tail head nodes g → ¬ InBox A g := by
  rw [rigid_iff_forall_graver_not_feasible tail head nodes A G hA]
  constructor
  · intro h g hg hbox
    refine h g hg ⟨?_, ?_, ?_⟩
    · exact pos_add_of_inbox hbox hA.1
    · exact BalancedZ.add tail head nodes hA.2.1 hg.2.1
    · have h1 : ∑ e ∈ Finset.univ, A e = G := hA.2.2
      have h2 : ∑ e ∈ Finset.univ, g e = 0 := hg.2.2.1
      show ∑ e ∈ Finset.univ, (A e + g e) = G
      simp only [Finset.sum_add_distrib]
      omega
  · intro h g hg hFeas
    refine h g hg ?_
    intro e
    have h1 : (1 : ℤ) ≤ A e + g e := hFeas.1 e
    show (1 - A e) ≤ g e
    omega

end GraverBasis

end AssemblyP1.GraverRigidity
